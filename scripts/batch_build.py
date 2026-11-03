#!/usr/bin/env python3
"""Resumable, budgeted build driver.

`offline_build.py` is incremental but re-attempts known-failing modules on every run,
and this environment caps a single command at ~300s. This driver keeps state in
`.build_state.json` so repeated invocations make forward progress:

  * modules that built successfully are skipped via their `.olean` (as before)
  * modules that failed are recorded with their diagnostics and skipped next time,
    unless their source has changed since the failure, or `--retry` is passed
  * it stops cleanly when the wall-clock budget is exhausted

Usage:
    python3 scripts/batch_build.py --targets FILE [--budget 260] [--retry MOD ...]
    python3 scripts/batch_build.py --report
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
STATE = os.path.join(ROOT, ".build_state.json")
CACHE_PARENT = os.environ.get("CRNT_CACHE", "")
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)


def src(m):
    return os.path.join(ROOT, m.replace(".", os.sep) + ".lean")


def olean(m):
    return os.path.join(BUILD, m.replace(".", os.sep) + ".olean")


def deps(m):
    p = src(m)
    if not os.path.exists(p):
        return []
    with open(p, encoding="utf-8", errors="replace") as fh:
        return IMPORT.findall(fh.read())


def closure(targets):
    order, state = [], {}

    def visit(m, stack):
        if state.get(m) == 1:
            return
        if state.get(m) == 0:
            return  # tolerate cycles here; check_imports is the real gate
        if not os.path.exists(src(m)):
            return
        state[m] = 0
        for d in deps(m):
            visit(d, stack + [m])
        state[m] = 1
        order.append(m)

    for t in targets:
        visit(t, [])
    return order


def lean_path():
    roots = []
    if CACHE_PARENT and os.path.isdir(CACHE_PARENT):
        for name in sorted(os.listdir(CACHE_PARENT)):
            d = os.path.join(CACHE_PARENT, name, ".lake", "build", "lib", "lean")
            if os.path.isdir(d):
                roots.append(d)
    roots.append(BUILD)
    return ":".join(roots)


def load_state():
    if os.path.exists(STATE):
        with open(STATE) as fh:
            return json.load(fh)
    return {"failed": {}}


def save_state(st):
    tmp = STATE + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh, indent=1, sort_keys=True)
    os.replace(tmp, STATE)


def up_to_date(m):
    ol, s = olean(m), src(m)
    if not os.path.exists(ol) or not os.path.exists(s):
        return False
    if os.path.getmtime(ol) < os.path.getmtime(s):
        return False
    for d in deps(m):
        dol = olean(d)
        if os.path.exists(dol) and os.path.getmtime(ol) < os.path.getmtime(dol):
            return False
    return True


def compile_module(m, env):
    base = os.path.join(BUILD, m.replace(".", os.sep))
    os.makedirs(os.path.dirname(base), exist_ok=True)
    t0 = time.time()
    proc = subprocess.run(
        ["lean", src(m), "-o", base + ".olean", "-i", base + ".ilean", "--root", ROOT],
        capture_output=True, text=True, env=env)
    return proc.returncode == 0, (proc.stdout + proc.stderr).strip(), time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets")
    ap.add_argument("--budget", type=float, default=260.0)
    ap.add_argument("--retry", nargs="*", default=[])
    ap.add_argument("--retry-all", action="store_true")
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args()

    st = load_state()
    failed = st["failed"]

    if args.report:
        print(f"recorded failures: {len(failed)}")
        rows = sorted(failed.items(), key=lambda kv: -kv[1].get("nerrors", 0))
        for m, info in rows:
            print(f"  {info.get('nerrors', 0):>3} err  {m}")
        return 0

    for m in args.retry:
        failed.pop(m, None)
    if args.retry_all:
        failed.clear()

    targets = [l.strip() for l in open(args.targets)
               if l.strip() and not l.startswith("#")]
    order = closure(targets)

    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path()

    t_start = time.time()
    built = skipped = skipped_failed = 0
    newly_failed = []

    for m in order:
        if time.time() - t_start > args.budget:
            print(f"-- budget exhausted, stopping (resume by rerunning)")
            break
        if up_to_date(m):
            skipped += 1
            continue
        rec = failed.get(m)
        if rec and os.path.exists(src(m)) and \
                abs(os.path.getmtime(src(m)) - rec.get("src_mtime", -1)) < 1e-6:
            skipped_failed += 1
            continue
        # a module whose dependency never built cannot be judged; skip quietly
        missing = [d for d in deps(m) if not os.path.exists(olean(d))]
        if missing:
            skipped_failed += 1
            continue
        ok, out, dt = compile_module(m, env)
        if ok:
            built += 1
            failed.pop(m, None)
            print(f"ok   {m}  ({dt:.1f}s)")
        else:
            n = len(re.findall(r"error:", out))
            failed[m] = {"nerrors": n, "src_mtime": os.path.getmtime(src(m)),
                         "diag": out[:4000]}
            newly_failed.append((m, n))
            print(f"FAIL {m}  ({n} errors, {dt:.1f}s)")

    save_state(st)
    print(f"\nbuilt {built}, cached {skipped}, skipped-known-bad {skipped_failed}, "
          f"newly-failed {len(newly_failed)}")
    print(f"total recorded failures: {len(failed)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

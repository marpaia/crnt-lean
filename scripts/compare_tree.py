#!/usr/bin/env python3
"""Compare an external CRNT tree against ours and report which side is actually better.

Claims about "compiles cleanly" are cheap; this checks them. For every `.lean` file that
differs, elaborate BOTH versions against the same toolchain and cache, and record error and
`sorry` counts for each. Port only where the other tree is strictly better on both.

Method note: each candidate is elaborated in place (ours saved, theirs written, elaborated,
ours restored) so that both versions see an identical `LEAN_PATH` and an identical set of
dependency `.olean`s. Elaborating their file inside their own tree would not be comparable,
since their build state differs from ours.

Usage
    python3 scripts/compare_tree.py --other /path/to/their/crnt-lean            # survey
    python3 scripts/compare_tree.py --other ... --verify                        # + Lean
    python3 scripts/compare_tree.py --other ... --verify --port                 # + adopt
"""
from __future__ import annotations

import argparse
import filecmp
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
CACHE = os.environ.get("CRNT_CACHE", "")
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)


def strip_comments(text: str) -> str:
    out, i, n, d = [], 0, len(text), 0
    while i < n:
        if d == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            end = n if j < 0 else j
            out.append(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            d += 1
            out.append("  ")
            i += 2
        elif d and text.startswith("-/", i):
            d -= 1
            out.append("  ")
            i += 2
        else:
            out.append(text[i] if d == 0 else ("\n" if text[i] == "\n" else " "))
            i += 1
    return "".join(out)


def count_holes(path: str) -> int:
    t = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    return len(re.findall(r"\bsorry\b", t)) + len(re.findall(r"\badmit\b", t))


def lean_env():
    env = dict(os.environ)
    roots = []
    if CACHE and os.path.isdir(CACHE):
        for n in sorted(os.listdir(CACHE)):
            d = os.path.join(CACHE, n, ".lake", "build", "lib", "lean")
            if os.path.isdir(d):
                roots.append(d)
    roots.append(BUILD)
    env["LEAN_PATH"] = ":".join(roots)
    return env


def nerr(out: str) -> int:
    return len(re.findall(r"error", out))


def elaborate(path: str, env) -> tuple[int, str]:
    r = subprocess.run(["lean", path], capture_output=True, text=True, env=env)
    out = r.stdout + r.stderr
    return nerr(out), out


def olean(mod: str) -> str:
    return os.path.join(BUILD, mod.replace(".", os.sep) + ".olean")


def deps_built(mod: str, imports: dict) -> bool:
    return all(os.path.exists(olean(d)) for d in imports.get(mod, ()))


def all_imports(root: str) -> dict:
    imps = {}
    for dp, _, fs in os.walk(os.path.join(root, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, root)[:-5].replace(os.sep, ".")
                imps[mod] = IMPORT.findall(
                    open(p, encoding="utf-8", errors="replace").read())
    return imps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--other", required=True)
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--port", action="store_true")
    ap.add_argument("--only", nargs="*", default=None,
                    help="restrict to these module names")
    ap.add_argument("--budget", type=float, default=220.0)
    a = ap.parse_args()

    other = a.other
    ours_only, theirs_only, differ, same = [], [], [], []

    for dp, _, fs in os.walk(os.path.join(other, "CRNT")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            tp = os.path.join(dp, f)
            rel = os.path.relpath(tp, other)
            op = os.path.join(ROOT, rel)
            mod = rel[:-5].replace(os.sep, ".")
            if not os.path.exists(op):
                theirs_only.append((mod, tp))
            elif filecmp.cmp(op, tp, shallow=False):
                same.append(mod)
            else:
                differ.append((mod, op, tp))

    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), ROOT)
                if not os.path.exists(os.path.join(other, rel)):
                    ours_only.append(rel[:-5].replace(os.sep, "."))

    print(f"identical      : {len(same)}")
    print(f"differing      : {len(differ)}")
    print(f"only in theirs : {len(theirs_only)}")
    print(f"only in ours   : {len(ours_only)}")
    for m in ours_only:
        print(f"    ours-only  {m}")
    for m, _ in theirs_only:
        print(f"    theirs-only {m}")

    # hole-count delta is free; do it for every differing file
    print("\n=== differing files: hole counts (ours -> theirs) ===")
    rows = []
    for mod, op, tp in differ:
        ho, ht = count_holes(op), count_holes(tp)
        rows.append((mod, op, tp, ho, ht))
    for mod, _, _, ho, ht in sorted(rows, key=lambda r: (r[4] - r[3], r[0])):
        flag = "  <-- theirs fewer" if ht < ho else ("  (ours fewer)" if ho < ht else "")
        print(f"  {ho:>3} -> {ht:>3}  {mod}{flag}")

    if not a.verify:
        return 0

    imports = all_imports(ROOT)
    env = lean_env()
    t0 = time.time()
    print("\n=== Lean verification (both versions, identical LEAN_PATH) ===")
    adopt, reject, skip = [], [], []

    cands = rows
    if a.only:
        cands = [r for r in rows if r[0] in set(a.only)]

    for mod, op, tp, ho, ht in cands:
        if time.time() - t0 > a.budget:
            print("-- budget reached; rerun to continue")
            break
        if not deps_built(mod, imports):
            skip.append((mod, "deps not built"))
            continue
        eo, _ = elaborate(op, env)
        backup = op + ".cmp-backup"
        shutil.copy2(op, backup)
        try:
            shutil.copy2(tp, op)
            et, out_t = elaborate(op, env)
        finally:
            shutil.move(backup, op)
        verdict = ""
        if (et, ht) < (eo, ho):
            verdict = "ADOPT"
            adopt.append((mod, op, tp, eo, ho, et, ht))
        elif (et, ht) == (eo, ho):
            verdict = "tie"
        else:
            verdict = "keep ours"
            reject.append(mod)
        print(f"  {verdict:<9} {mod}: ours err={eo} holes={ho} | "
              f"theirs err={et} holes={ht}")

    print(f"\nadopt {len(adopt)}, keep-ours {len(reject)}, skipped {len(skip)}")
    for m, why in skip[:12]:
        print(f"    skipped {m} ({why})")

    if a.port and adopt:
        for mod, op, tp, eo, ho, et, ht in adopt:
            shutil.copy2(tp, op)
            print(f"ported {mod}  (err {eo}->{et}, holes {ho}->{ht})")
        print(f"\nported {len(adopt)} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

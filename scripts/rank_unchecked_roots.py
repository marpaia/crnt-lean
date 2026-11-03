#!/usr/bin/env python3
"""Rank the non-elaborating modules by how much UNCHECKED they gate.

`audit_unchecked.py` found 804 statements with no static red flag: they can only be settled
by making their modules elaborate. That is 156 modules, but most are not independent
problems -- they sit behind a small number of roots. This separates them:

  DEP-BLOCKED   every own error is `object file ... does not exist`; nothing to fix here,
                it compiles for free once its roots do.
  ROOT          has real errors of its own AND all of its dependencies already build, so it
                is actionable right now.
  DEEP          has real errors but also unbuilt dependencies; fix the roots first.

Each ROOT is scored by the number of UNCHECKED statements in its transitive downstream
closure, which is the number of unverified claims that elaborating it would settle.

State is kept in `.elab_state.json`, so repeated runs make progress under the ~300s
per-command cap.

    python3 scripts/rank_unchecked_roots.py --budget 200     # measure (resumable)
    python3 scripts/rank_unchecked_roots.py --report         # ranked roots
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
STATE = os.path.join(ROOT, ".elab_state.json")
CACHE = os.environ.get("CRNT_CACHE", "")
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)", re.M)
MISSING_OBJ = re.compile(r"object file '[^']*' of module (\S+) does not exist")


def strip_comments(text):
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


def src(m):
    return os.path.join(ROOT, m.replace(".", os.sep) + ".lean")


def olean(m):
    return os.path.join(BUILD, m.replace(".", os.sep) + ".olean")


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


def scan():
    imports, unchecked_ct = {}, {}
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
            raw = open(p, encoding="utf-8", errors="replace").read()
            imports[m] = IMPORT.findall(raw)
            code = strip_comments(raw)
            n = 0
            starts = [(mm.start(), mm.group(2)) for mm in DECL.finditer(code)]
            for idx, (pos, _) in enumerate(starts):
                end = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
                if not re.search(r"\bsorry\b", code[pos:end]):
                    n += 1
            unchecked_ct[m] = 0 if os.path.exists(olean(m)) else n
    return imports, unchecked_ct


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--budget", type=float, default=200.0)
    ap.add_argument("--report", action="store_true")
    a = ap.parse_args()

    imports, unchecked_ct = scan()
    consumers = defaultdict(set)
    for m, deps in imports.items():
        for d in deps:
            consumers[d].add(m)

    state = json.load(open(STATE)) if os.path.exists(STATE) else {}
    targets = [m for m in imports if not os.path.exists(olean(m))]
    env = lean_env()

    if not a.report:
        t0 = time.time()
        done = 0
        for m in targets:
            if time.time() - t0 > a.budget:
                print(f"-- budget reached after {done} module(s); rerun to continue")
                break
            mt = os.path.getmtime(src(m))
            if m in state and abs(state[m].get("mtime", -1) - mt) < 1e-6:
                continue
            r = subprocess.run(["lean", src(m)], capture_output=True, text=True, env=env)
            out = r.stdout + r.stderr
            errs = [l for l in out.split("\n") if "error" in l]
            missing = set(MISSING_OBJ.findall(out))
            real = [l for l in errs if not MISSING_OBJ.search(l)]
            state[m] = {"mtime": mt, "nerr": len(errs), "nreal": len(real),
                        "missing": sorted(missing)}
            done += 1
        with open(STATE, "w") as fh:
            json.dump(state, fh, indent=1, sort_keys=True)
        print(f"measured {done}; total recorded {len(state)}/{len(targets)}")

    def downstream(m):
        seen, stack = set(), [m]
        while stack:
            c = stack.pop()
            for x in consumers.get(c, ()):
                if x not in seen:
                    seen.add(x)
                    stack.append(x)
        return seen

    dep_blocked, roots, deep = [], [], []
    for m, info in state.items():
        if info["nreal"] == 0 and info["missing"]:
            dep_blocked.append(m)
        elif info["nreal"] > 0:
            unbuilt = [d for d in imports.get(m, ()) if not os.path.exists(olean(d))]
            (deep if unbuilt else roots).append(m)

    scored = []
    for m in roots:
        gate = unchecked_ct.get(m, 0) + sum(unchecked_ct.get(x, 0) for x in downstream(m))
        scored.append((gate, state[m]["nreal"], m))
    scored.sort(key=lambda t: (-t[0], t[1]))

    print(f"\nnon-elaborating modules recorded : {len(state)}")
    print(f"  DEP-BLOCKED (free once roots build): {len(dep_blocked)}")
    print(f"  ROOT        (actionable now)       : {len(roots)}")
    print(f"  DEEP        (behind other roots)   : {len(deep)}")
    print(f"\nROOTs by UNCHECKED statements gated:")
    print(f"{'gates':>6} {'errs':>5}  module")
    for gate, nreal, m in scored[:30]:
        print(f"{gate:>6} {nreal:>5}  {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Promote ledger modules into the verified core — atomically.

Promotion touches files that must stay mutually consistent, and `check_exclusions.py`
fails loudly if they drift:

    scripts/unverified_modules.txt   drop the promoted entries
    CRNT.lean                        add imports, BEFORE the module docstring
    lakefile.toml                    regenerate from the ledger
    CRNTFrontier.lean                regenerate from the ledger + frontier history

Doing that by hand is how they drift. This snapshots every file first, applies the
change, runs `gen_lakefile.py` and all four gates, and **restores the snapshot if anything
fails**, so a bad promotion cannot leave the tree half-edited.

Two things this deliberately does *not* do, because both used to happen here and both
quietly destroyed the guard rails:

  * It does not lower `scripts/unverified_baseline.txt`.  That file is the high-water
    mark the growth guard compares against; auto-lowering it on every promotion means
    a promotion can be undone by re-adding the same number of bad modules.  Only the
    certified path, `scripts/close_hole.sh`, may lower it.
  * It does not delete the promoted module's `import` from `CRNTFrontier.lean`.  The
    frontier target is the thing whose elaboration-error count is the progress metric;
    dropping a module from it the moment the module is verified is how the metric
    silently stops measuring it.  `CRNTFrontier.lean` is generated, and a graduating
    module moves to `scripts/frontier_history.txt` instead of disappearing.

Eligibility is not taken on trust: a module may be promoted only if its `.olean` exists
(Lean has actually checked it) and its whole transitive import closure is `sorry`-free.

Usage
    python3 scripts/promote.py --dry-run
    python3 scripts/promote.py --all
    python3 scripts/promote.py CRNT.Flux.Cone CRNT.Oscillation.Analyze
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
BASELINE = os.path.join(ROOT, "scripts", "unverified_baseline.txt")
HISTORY = os.path.join(ROOT, "scripts", "frontier_history.txt")
UMBRELLA = os.path.join(ROOT, "CRNT.lean")
FRONTIER = os.path.join(ROOT, "CRNTFrontier.lean")
LAKEFILE = os.path.join(ROOT, "lakefile.toml")
TOUCHED = [LEDGER, BASELINE, HISTORY, UMBRELLA, FRONTIER, LAKEFILE]
GATES = ["check_imports", "check_stubs", "check_undefined_names", "check_exclusions"]

IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
SORRY = re.compile(r"\bsorry\b")


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


def src(m):
    return os.path.join(ROOT, m.replace(".", os.sep) + ".lean")


def olean(m):
    return os.path.join(BUILD, m.replace(".", os.sep) + ".olean")


def scan():
    imports, sorries = {}, {}
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                t = open(p, encoding="utf-8", errors="replace").read()
                imports[m] = IMPORT.findall(t)
                sorries[m] = len(SORRY.findall(strip_comments(t)))
    return imports, sorries


def import_closure(entry, imports=None):
    """Every `CRNT.*` module transitively imported by `entry` (itself excluded)."""
    if imports is None:
        imports, _ = scan()
    seen, stack = set(), [entry]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for d in imports.get(m, ()):
            if d not in seen:
                stack.append(d)
    seen.discard(entry)
    return seen


def closure_clean(m, imports, sorries, memo, stack=frozenset()):
    if m in memo:
        return memo[m]
    if m in stack:
        return True
    if sorries.get(m, 0) > 0:
        memo[m] = False
        return False
    r = all(closure_clean(d, imports, sorries, memo, stack | {m})
            for d in imports.get(m, ()))
    memo[m] = r
    return r


def read_ledger():
    out = []
    with open(LEDGER, encoding="utf-8") as fh:
        for line in fh:
            t = line.strip()
            if t and not t.startswith("#"):
                out.append(t)
    return out


def eligible():
    imports, sorries = scan()
    memo = {}
    ok = []
    for m in read_ledger():
        if os.path.exists(olean(m)) and closure_clean(m, imports, sorries, memo):
            ok.append(m)
    return ok


def snapshot():
    return {p: open(p, "rb").read() for p in TOUCHED if os.path.exists(p)}


def restore(snap):
    for p, data in snap.items():
        with open(p, "wb") as fh:
            fh.write(data)


def apply_promotion(mods):
    mset = set(mods)

    # 1. ledger
    lines = open(LEDGER, encoding="utf-8").read().split("\n")
    kept = [l for l in lines if l.strip() not in mset]
    open(LEDGER, "w", encoding="utf-8").write("\n".join(kept))

    # 2. umbrella — insert after the LAST `import CRNT...`, which keeps the new imports
    #    ahead of the module docstring.  An import after the docstring parses fine in
    #    isolation and only breaks in the umbrella.  Modules already reachable from
    #    `CRNT.lean` are left alone: re-importing them would duplicate the line.
    reachable = import_closure("CRNT")
    fresh = [m for m in sorted(mset) if m not in reachable]
    if fresh:
        ul = open(UMBRELLA, encoding="utf-8").read().split("\n")
        imports_at = [i for i, l in enumerate(ul) if l.startswith("import CRNT")]
        at = (imports_at[-1] + 1) if imports_at else 0
        block = ["", "-- Promoted from the frontier ledger (elaborated, closure sorry-free)."]
        block += [f"import {m}" for m in fresh]
        ul[at:at] = block
        open(UMBRELLA, "w", encoding="utf-8").write("\n".join(ul))

    # 3. baseline: deliberately untouched.  See the module docstring — only
    #    `scripts/close_hole.sh`, which additionally certifies the axioms and the
    #    build, is allowed to lower the growth guard.

    # 4. CRNTFrontier.lean is *generated* from the ledger plus
    #    `scripts/frontier_history.txt`; `gen_lakefile.py` (run by main) rewrites it and
    #    appends the promoted modules to the history, so the frontier target keeps
    #    elaborating them and its error count keeps measuring them.
    return len(read_ledger())


def run(cmd):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("modules", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    elig = eligible()
    if a.all:
        mods = elig
    elif a.modules:
        mods = a.modules
        bad = [m for m in mods if m not in elig]
        if bad:
            print("NOT eligible (needs .olean + sorry-free closure):")
            for m in bad:
                print("  ", m)
            return 1
    else:
        mods = []

    print(f"eligible for promotion: {len(elig)}")
    for m in sorted(elig):
        print(f"  {'->' if m in mods else '  '} {m}")
    if a.dry_run or not mods:
        print("\n(dry run — nothing written)")
        return 0

    snap = snapshot()
    try:
        remaining = apply_promotion(mods)
        print(f"\nledger {len(read_ledger()) + len(mods)} -> {remaining}")

        r = run([sys.executable, "scripts/gen_lakefile.py"])
        if r.returncode != 0:
            print("gen_lakefile FAILED\n" + r.stdout + r.stderr)
            raise RuntimeError("gen_lakefile")

        failed = []
        for g in GATES:
            r = run([sys.executable, f"scripts/{g}.py"])
            ok = r.returncode == 0
            print(f"  {g:24} {'PASS' if ok else 'FAIL'}")
            if not ok:
                failed.append(g)
                print("    " + (r.stdout + r.stderr).strip()[-500:])
        if failed:
            raise RuntimeError("gates: " + ", ".join(failed))
    except Exception as exc:
        restore(snap)
        print(f"\nROLLED BACK — {exc}")
        return 1

    print(f"\npromoted {len(mods)} module(s); all gates green")
    return 0


if __name__ == "__main__":
    sys.exit(main())

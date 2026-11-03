#!/usr/bin/env python3
"""Rank ledgered modules by repair leverage.

For each module on the frontier ledger, report whether it is `sorry`-free and how
many *other* sorry-free ledgered modules sit transitively downstream of it. A module
whose own dependencies are all clean is "ready": it can be attempted right now.
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
# `sorry` as a token, ignoring occurrences inside line comments and doc comments
SORRY = re.compile(r"\bsorry\b")


def src(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def read(mod: str) -> str:
    p = src(mod)
    if not os.path.exists(p):
        return ""
    with open(p, encoding="utf-8", errors="replace") as fh:
        return fh.read()


def strip_comments(text: str) -> str:
    """Remove -- line comments and /- ... -/ block comments (incl. /-! docs)."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    ledger_path = os.path.join(ROOT, "scripts", "unverified_modules.txt")
    ledger = []
    with open(ledger_path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line and not line.startswith("#"):
                ledger.append(line)
    ledger_set = set(ledger)

    # discover every module on disk
    all_mods = []
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "CRNT")):
        for f in files:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, f), ROOT)
                all_mods.append(rel[:-5].replace(os.sep, "."))

    imports: dict[str, list[str]] = {}
    sorries: dict[str, int] = {}
    for m in all_mods:
        text = read(m)
        imports[m] = IMPORT.findall(text)
        sorries[m] = len(SORRY.findall(strip_comments(text)))

    # reverse edges: dep -> consumers
    consumers: dict[str, set[str]] = defaultdict(set)
    for m, deps in imports.items():
        for d in deps:
            consumers[d].add(m)

    def downstream(mod: str) -> set[str]:
        seen: set[str] = set()
        stack = [mod]
        while stack:
            cur = stack.pop()
            for c in consumers.get(cur, ()):
                if c not in seen:
                    seen.add(c)
                    stack.append(c)
        return seen

    # transitive-closure sorry check
    memo: dict[str, bool] = {}

    def closure_clean(mod: str, stack: frozenset[str] = frozenset()) -> bool:
        if mod in memo:
            return memo[mod]
        if mod in stack:
            return True  # cycle guard; check_imports already rejects real cycles
        if sorries.get(mod, 0) > 0:
            memo[mod] = False
            return False
        ok = all(closure_clean(d, stack | {mod}) for d in imports.get(mod, ()))
        memo[mod] = ok
        return ok

    clean_ledger = [m for m in ledger if sorries.get(m, 0) == 0]
    sorry_ledger = [(m, sorries[m]) for m in ledger if sorries.get(m, 0) > 0]

    rows = []
    for m in clean_ledger:
        deps_on_ledger = [d for d in imports[m] if d in ledger_set]
        ready = all(d not in ledger_set for d in imports[m])
        blocked_clean = len(downstream(m) & set(clean_ledger))
        blocked_any = len(downstream(m) & ledger_set)
        rows.append((blocked_clean, blocked_any, m, ready, deps_on_ledger))

    rows.sort(key=lambda r: (-r[0], -r[1], r[2]))

    print(f"ledger              : {len(ledger)} modules")
    print(f"  sorry-free        : {len(clean_ledger)}  <- mechanical worklist")
    print(f"  containing sorry  : {len(sorry_ledger)}  "
          f"({sum(c for _, c in sorry_ledger)} sorries)")
    print(f"tree-wide sorries   : {sum(sorries.values())}")
    print(f"closure-clean & off-ledger modules: "
          f"{sum(1 for m in all_mods if m not in ledger_set and closure_clean(m))}")
    print()
    print("READY sorry-free ledger modules (no ledgered dependency), by leverage:")
    print(f"{'blocks(clean)':>13} {'blocks(any)':>11}  module")
    shown = 0
    for bc, ba, m, ready, _ in rows:
        if ready:
            print(f"{bc:>13} {ba:>11}  {m}")
            shown += 1
            if shown >= 25:
                break
    print()
    print("NOT-ready sorry-free ledger modules with highest leverage:")
    shown = 0
    for bc, ba, m, ready, dl in rows:
        if not ready:
            print(f"{bc:>13} {ba:>11}  {m}   (waits on {len(dl)}: {', '.join(dl[:3])})")
            shown += 1
            if shown >= 10:
                break
    return 0


if __name__ == "__main__":
    sys.exit(main())

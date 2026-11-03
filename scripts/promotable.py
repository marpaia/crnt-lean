#!/usr/bin/env python3
"""List ledgered modules that are now promotable.

A ledger entry may leave the frontier only when both hold:
  1. it elaborates (its `.olean` exists in the project build tree), and
  2. its entire transitive import closure is `sorry`-free.

Condition 2 is the one that bites: a module can be `sorry`-free itself and still be
unpromotable because something it imports is not.
"""
from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
SORRY = re.compile(r"\bsorry\b")


def src(m):
    return os.path.join(ROOT, m.replace(".", os.sep) + ".lean")


def olean(m):
    return os.path.join(BUILD, m.replace(".", os.sep) + ".olean")


def strip_comments(text):
    out, i, n, d = [], 0, len(text), 0
    while i < n:
        if d == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            d += 1
            i += 2
        elif d and text.startswith("-/", i):
            d -= 1
            i += 2
        else:
            if d == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def main():
    mods = []
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), ROOT)
                mods.append(rel[:-5].replace(os.sep, "."))

    imports, sorries = {}, {}
    for m in mods:
        t = open(src(m), encoding="utf-8", errors="replace").read()
        imports[m] = IMPORT.findall(t)
        sorries[m] = len(SORRY.findall(strip_comments(t)))

    memo = {}

    def clean(m, stack=frozenset()):
        if m in memo:
            return memo[m]
        if m in stack:
            return True
        if sorries.get(m, 0) > 0:
            memo[m] = False
            return False
        r = all(clean(d, stack | {m}) for d in imports.get(m, ()))
        memo[m] = r
        return r

    ledger = [l.strip() for l in
              open(os.path.join(ROOT, "scripts", "unverified_modules.txt"))
              if l.strip() and not l.startswith("#")]

    promotable, built_not_clean, clean_not_built, neither = [], [], [], []
    for m in ledger:
        b = os.path.exists(olean(m))
        c = clean(m)
        if b and c:
            promotable.append(m)
        elif b and not c:
            built_not_clean.append(m)
        elif c and not b:
            clean_not_built.append(m)
        else:
            neither.append(m)

    print(f"ledger: {len(ledger)}")
    print(f"  PROMOTABLE (builds + closure sorry-free): {len(promotable)}")
    print(f"  builds, but closure has a sorry          : {len(built_not_clean)}")
    print(f"  closure clean, but does not build        : {len(clean_not_built)}")
    print(f"  neither                                  : {len(neither)}")
    print()
    for m in sorted(promotable):
        print(m)
    if "-v" in sys.argv:
        print("\n-- closure clean but not building --")
        for m in sorted(clean_not_built):
            print(" ", m)
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Find `sorry`ed declarations whose *statement* is already proved somewhere else.

HANDOFF §7.1: four times in this project a `sorry` sat next to an existing proof, the worst
being `deficiencyOne_uniqueness` (sorried) versus `deficiencyOneUniqueness_multiClass`
(proved, identical statement, weaker hypotheses). Name matching finds almost none of these,
so match on the normalized statement text instead.

Normalization strips the declaration name, binder names, whitespace and implicit/instance
brackets, then groups. A group containing both a sorried and a proved member is a candidate
for transferring the proof.
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([^\s:({\[]+)")


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
            if d == 0:
                out.append(text[i])
            else:
                out.append("\n" if text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def normalize(stmt: str) -> str:
    """Collapse a statement to a comparable skeleton."""
    s = stmt
    # drop binder *names*, keeping their types: `(hx : x.Positive)` -> `(: x.Positive)`
    s = re.sub(r"([({\[])\s*[^:()\[\]{}]*?\s*:", r"\1:", s)
    s = re.sub(r"\s+", "", s)
    return s


def collect():
    """Return list of (module, name, normalized_stmt, has_sorry, raw_block)."""
    out = []
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dp, f)
            mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
            raw = open(path, encoding="utf-8", errors="replace").read()
            code = strip_comments(raw)
            clines = code.split("\n")
            rlines = raw.split("\n")
            starts = [i for i, l in enumerate(clines) if DECL_START.match(l)]
            for idx, i in enumerate(starts):
                end = starts[idx + 1] if idx + 1 < len(starts) else len(clines)
                block_code = "\n".join(clines[i:end])
                block_raw = "\n".join(rlines[i:end])
                name = DECL_START.match(clines[i]).group(2)
                # statement = text up to the proof marker
                m = re.search(r":=\s*by\b|:=", block_code)
                stmt = block_code[:m.start()] if m else block_code
                # remove the leading keyword + name
                stmt = re.sub(r"^.*?(theorem|lemma)\s+\S+", "", stmt, count=1,
                              flags=re.S)
                has_sorry = bool(re.search(r"\bsorry\b", block_code))
                out.append((mod, name, normalize(stmt), has_sorry, block_raw, i + 1))
    return out


def main():
    decls = collect()
    bodies = {(mod, name): raw for mod, name, _, _, raw, _ in decls}
    groups = defaultdict(list)
    for mod, name, norm, has_sorry, raw, line in decls:
        if len(norm) < 40:          # too short to be a meaningful match
            continue
        groups[norm].append((mod, name, has_sorry, line))

    transferable, dup_sorries, delegations = [], [], []
    for norm, members in groups.items():
        if len(members) < 2:
            continue
        sorried = [m for m in members if m[2]]
        proved = [m for m in members if not m[2]]
        if sorried and proved:
            # A "proved" member whose proof body merely cites a sorried member of the same
            # group has proved nothing.  This produced a false positive on
            # `number_independent_complexBalance_constraints`, which is literally
            # `N.finrank_complexBalanceObstructionSpace`.
            sorried_names = {m[1] for m in sorried}
            real = []
            for pm in proved:
                body = bodies.get((pm[0], pm[1]), "")
                m = re.search(r":=", body)
                proof = body[m.start():] if m else body
                if any(re.search(r"\b" + re.escape(sn) + r"\b", proof)
                       for sn in sorried_names):
                    delegations.append((norm, sorried, pm))
                else:
                    real.append(pm)
            if real:
                transferable.append((norm, sorried, real))
        elif len(sorried) > 1:
            dup_sorries.append((norm, sorried))

    print("=" * 90)
    print(f"TRANSFERABLE: {len(transferable)} statement group(s) with both a "
          f"sorried and a proved member")
    print("=" * 90)
    for norm, sorried, proved in transferable:
        print("\n--- sorried:")
        for mod, name, _, line in sorried:
            print(f"      {mod}:{line}  {name}")
        print("    proved:")
        for mod, name, _, line in proved:
            print(f"      {mod}:{line}  {name}")
        print(f"    stmt: {norm[:220]}")

    print()
    print("=" * 90)
    print(f"DELEGATIONS REJECTED: {len(delegations)} (a 'proved' twin that just cites the sorry)")
    print("=" * 90)
    for norm, sorried, pm in delegations:
        print(f"    {pm[0]}:{pm[3]}  {pm[1]}  -> cites {[s[1] for s in sorried]}")

    print()
    print("=" * 90)
    print(f"DUPLICATED SORRIES: {len(dup_sorries)} statement group(s) sorried in "
          f"2+ places (dedup lowers the count without proving anything)")
    print("=" * 90)
    for norm, sorried in dup_sorries:
        print("\n---")
        for mod, name, _, line in sorried:
            print(f"      {mod}:{line}  {name}")
        print(f"    stmt: {norm[:200]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

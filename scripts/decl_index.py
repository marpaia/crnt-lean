#!/usr/bin/env python3
"""Declaration index for crnt-lean: query before you write.

Motivation: `crossClassRatio_eq_iff_robust` was already proved in
`Design/ACRCrossClass.lean` *and* described in `docs/multistationarity-robustness.md`, and it
still got reinvented in `Deficiency/LogMonomialRatio.lean`. The area docs are prose and
partial; `docs/file-lists.md` indexes modules but not declarations. Nothing indexed
*statements*, which is what you need to notice a duplicate.

This is generated from source, so it cannot drift. Regenerate it whenever declarations move.

Usage
    python3 scripts/decl_index.py --build            # write docs/theorem-index.md
    python3 scripts/decl_index.py --find ratio_eq    # substring match on names
    python3 scripts/decl_index.py --like 'logMonomialRatio x y c = logMonomialRatio x y d'
    python3 scripts/decl_index.py --dups             # proved statements appearing 2+ times
    python3 scripts/decl_index.py --open             # every sorried declaration

`--like` is the duplicate check: it normalizes away binder names and whitespace and reports
anything whose statement skeleton overlaps. Run it before adding a lemma.
"""
from __future__ import annotations

import argparse
import difflib
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
OUT = os.path.join(ROOT, "docs", "theorem-index.md")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
    r"([^\s:({\[]+)")


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


def normalize(stmt: str) -> str:
    s = re.sub(r"([({\[])\s*[^:()\[\]{}]*?\s*:", r"\1:", stmt)
    return re.sub(r"\s+", "", s)


def olean(mod: str) -> str:
    return os.path.join(BUILD, mod.replace(".", os.sep) + ".olean")


def collect():
    """Yield dicts describing every declaration in CRNT/."""
    recs = []
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dp, f)
            mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
            raw = open(path, encoding="utf-8", errors="replace").read()
            code = strip_comments(raw)
            clines, rlines = code.split("\n"), raw.split("\n")
            starts = [i for i, l in enumerate(clines) if DECL.match(l)]
            built = os.path.exists(olean(mod))
            for idx, i in enumerate(starts):
                end = starts[idx + 1] if idx + 1 < len(starts) else len(clines)
                block = "\n".join(clines[i:end])
                m = DECL.match(clines[i])
                kind, name = m.group(1), m.group(2)
                sm = re.search(r":=\s*by\b|:=", block)
                stmt = block[:sm.start()] if sm else block
                stmt = re.sub(r"^.*?(theorem|lemma|def|abbrev|structure|inductive|"
                              r"instance|class)\s+\S+", "", stmt, count=1, flags=re.S)
                has_sorry = bool(re.search(r"\bsorry\b", block))
                recs.append({
                    "mod": mod, "line": i + 1, "kind": kind, "name": name,
                    "stmt": " ".join(stmt.split()), "norm": normalize(stmt),
                    "sorry": has_sorry, "built": built,
                })
    return recs


def status(r) -> str:
    if r["sorry"]:
        return "SORRY"
    return "PROVED" if r["built"] else "UNCHECKED"


def cmd_find(recs, pat):
    pat = pat.lower()
    hits = [r for r in recs if pat in r["name"].lower()]
    print(f"{len(hits)} name match(es) for {pat!r}\n")
    for r in sorted(hits, key=lambda r: (r["mod"], r["line"])):
        print(f"[{status(r):9}] {r['mod']}:{r['line']}  {r['kind']} {r['name']}")
        if r["stmt"]:
            print(f"              {r['stmt'][:150]}")


def cmd_like(recs, stmt):
    target = normalize(stmt)
    scored = []
    for r in recs:
        if not r["norm"]:
            continue
        ratio = difflib.SequenceMatcher(None, target, r["norm"]).ratio()
        if ratio > 0.55 or target in r["norm"] or r["norm"] in target:
            scored.append((ratio, r))
    scored.sort(key=lambda t: -t[0])
    if not scored:
        print("no similar statement found -- safe to add")
        return
    print(f"{len(scored)} similar statement(s) -- CHECK BEFORE ADDING\n")
    for ratio, r in scored[:15]:
        print(f"  {ratio:.2f} [{status(r):9}] {r['mod']}:{r['line']}  {r['name']}")


def cmd_dups(recs):
    groups = defaultdict(list)
    for r in recs:
        if r["kind"] in ("theorem", "lemma") and len(r["norm"]) >= 40:
            groups[r["norm"]].append(r)
    n = 0
    for norm, ms in groups.items():
        proved = [m for m in ms if not m["sorry"]]
        if len(ms) < 2 or not proved:
            continue
        n += 1
        print("---")
        for m in ms:
            print(f"  [{status(m):9}] {m['mod']}:{m['line']}  {m['name']}")
        print(f"  stmt: {norm[:180]}")
    print(f"\n{n} duplicated statement group(s)")


def cmd_open(recs):
    hits = [r for r in recs if r["sorry"]]
    by_mod = defaultdict(list)
    for r in hits:
        by_mod[r["mod"]].append(r)
    print(f"{len(hits)} declaration(s) carrying `sorry`, in {len(by_mod)} module(s)\n")
    for mod in sorted(by_mod):
        print(f"{mod}")
        for r in by_mod[mod]:
            print(f"   :{r['line']:<5} {r['name']}")


def cmd_build(recs):
    thms = [r for r in recs if r["kind"] in ("theorem", "lemma")]
    proved = [r for r in thms if status(r) == "PROVED"]
    unchecked = [r for r in thms if status(r) == "UNCHECKED"]
    sorried = [r for r in thms if r["sorry"]]

    by_area = defaultdict(list)
    for r in recs:
        by_area[r["mod"].split(".")[1] if r["mod"].count(".") >= 1 else "?"].append(r)

    lines = []
    w = lines.append
    w("# Declaration index (generated)")
    w("")
    w("Generated by `scripts/decl_index.py --build`. **Do not hand-edit.**")
    w("")
    w("`PROVED` = no `sorry` and its module has an `.olean` (Lean has checked it).  ")
    w("`UNCHECKED` = no `sorry` in the text, but the module does not elaborate, so the "
      "proof has **never been verified** -- treat as unproved.  ")
    w("`SORRY` = carries an explicit `sorry`.")
    w("")
    w("The `UNCHECKED` distinction matters: several statements in this tree look proved but "
      "sit in modules that have never compiled, and at least one of those 'proofs' turned "
      "out to reference struct fields that do not exist.")
    w("")
    w("## Before adding a lemma")
    w("")
    w("```")
    w("python3 scripts/decl_index.py --like '<your statement>'")
    w("python3 scripts/decl_index.py --find <keyword>")
    w("```")
    w("")
    w("`crossClassRatio_eq_iff_robust` was already proved *and* documented in prose, and "
      "still got reinvented. Names diverge; statements do not.")
    w("")
    w("## Totals")
    w("")
    w(f"| | count |")
    w(f"|---|---|")
    w(f"| theorems/lemmas | {len(thms)} |")
    w(f"| PROVED | {len(proved)} |")
    w(f"| UNCHECKED (module never elaborated) | {len(unchecked)} |")
    w(f"| SORRY | {len(sorried)} |")
    w(f"| all declarations | {len(recs)} |")
    w("")
    w("## Open obligations, by module")
    w("")
    by_mod = defaultdict(list)
    for r in sorried:
        by_mod[r["mod"]].append(r)
    for mod in sorted(by_mod):
        w(f"- **{mod}**")
        for r in by_mod[mod]:
            w(f"  - `{r['name']}` (:{r['line']})")
    w("")
    w("## Theorems and lemmas, by area")
    w("")
    for area in sorted(by_area):
        rs = [r for r in by_area[area] if r["kind"] in ("theorem", "lemma")]
        if not rs:
            continue
        w(f"### {area} ({len(rs)})")
        w("")
        for r in sorted(rs, key=lambda r: (r["mod"], r["line"])):
            w(f"- `{r['name']}` — {status(r)} — `{r['mod']}:{r['line']}`")
        w("")

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    print(f"wrote {OUT}")
    print(f"  theorems/lemmas {len(thms)}  PROVED {len(proved)}  "
          f"UNCHECKED {len(unchecked)}  SORRY {len(sorried)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--find")
    ap.add_argument("--like")
    ap.add_argument("--dups", action="store_true")
    ap.add_argument("--open", action="store_true", dest="open_")
    a = ap.parse_args()
    recs = collect()
    if a.find:
        cmd_find(recs, a.find)
    elif a.like:
        cmd_like(recs, a.like)
    elif a.dups:
        cmd_dups(recs)
    elif a.open_:
        cmd_open(recs)
    else:
        cmd_build(recs)
    return 0


if __name__ == "__main__":
    sys.exit(main())

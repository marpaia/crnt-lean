#!/usr/bin/env python3
"""Flag repository identifiers that are used but never declared.

Motivation: a source drop that has not been elaborated can reference helper
lemmas that were never written.  That is not a `sorry`, so the sorry-grep passes;
the tree simply fails to build.  Three such names existed in the oscillation
development when this script was written, all of them load-bearing:

    constructTransverseFloquetSectionData        (FloquetOrbitalStability.lean)
    constructParameterizedPoincarePersistence    (FloquetPersistenceGeneral.lean)
    massActionFloquetData_of_branchMonodromy     (FloquetPersistenceGeneral.lean)

This is a cheap pre-merge gate; it is not a substitute for `lake build`, which
remains the only real check.  It cannot see Mathlib, so it only reports names
that look like this project's own vocabulary (see scripts/repo_vocabulary.txt)
and are not on the external allowlist (scripts/external_names.txt).

Usage:
    python3 scripts/check_undefined_names.py            # exit 1 if anything is flagged
    python3 scripts/check_undefined_names.py --all      # also list presumed-external unknowns
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VOCAB = os.path.join(ROOT, "scripts", "repo_vocabulary.txt")
ALLOW = os.path.join(ROOT, "scripts", "external_names.txt")
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
GAPS = os.path.join(ROOT, "scripts", "frontier_gaps.txt")

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
# Structure fields and `where`-block entries become projections, so they count as declared.
FIELD = re.compile(r"^\s{2,}([a-zA-Z_][A-Za-z0-9_']*)\s*:")
# Anonymous-constructor field assignments (`foo := ...`) inside `where` blocks.
ASSIGN = re.compile(r"^\s{2,}([a-zA-Z_][A-Za-z0-9_']*)\s*:=")

# Identifier shapes that are almost always this project's own naming conventions.
REFERENCE = [
    re.compile(r"\b(construct[A-Z][A-Za-z0-9_']*)"),
    re.compile(r"\b([A-Za-z][A-Za-z0-9_']*_proved)\b"),
    re.compile(r"\b([A-Za-z][A-Za-z0-9_']*Target)\b"),
    re.compile(r"\b([A-Za-z][A-Za-z0-9_']*Bundle)\b"),
    re.compile(r"\b([a-z][A-Za-z0-9']*_of_[A-Za-z0-9_']+)\b"),
]


def read_list(path: str) -> list[str]:
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]


def lean_files() -> list[str]:
    out = []
    for d in ("CRNT", "test"):
        for base, _, files in os.walk(os.path.join(ROOT, d)):
            for f in files:
                if f.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(base, f), ROOT))
    for f in ("CRNT.lean", "Analyze.lean"):
        if os.path.exists(os.path.join(ROOT, f)):
            out.append(f)
    return sorted(out)


def strip_comments(text: str) -> str:
    """Blank comments, and blank `import` lines: a module path is not a term reference."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    return re.sub(r"^\s*import\s+[\w.]+", "", text, flags=re.M)


def unverified_paths() -> set[str]:
    """Files belonging to the frontier target, by relative path."""
    out: set[str] = set()
    if os.path.exists(LEDGER):
        with open(LEDGER, encoding="utf-8") as fh:
            for ln in fh:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    out.add(ln.replace(".", os.sep) + ".lean")
    out.add("CRNTFrontier.lean")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true",
                    help="also list unknown names that do not match repo vocabulary")
    ap.add_argument("--write-gaps", action="store_true",
                    help="rewrite scripts/frontier_gaps.txt from the current tree")
    args = ap.parse_args()
    frontier = unverified_paths()

    vocab = read_list(VOCAB)
    allow = set(read_list(ALLOW))

    sources = {}
    declared: set[str] = set()
    for path in lean_files():
        with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as fh:
            raw = fh.read()
        sources[path] = strip_comments(raw)
        for line in raw.split("\n"):
            for pat in (DECL, FIELD, ASSIGN):
                m = pat.match(line)
                if m:
                    declared.add(m.group(1).split(".")[-1])
                    break

    flagged: dict[str, tuple[str, int]] = {}
    unknown: dict[str, tuple[str, int]] = {}
    for path, text in sources.items():
        for lineno, line in enumerate(text.split("\n"), start=1):
            for pat in REFERENCE:
                for m in pat.finditer(line):
                    name = m.group(1)
                    short = name.split(".")[-1]
                    if short in declared or name in allow or short in allow:
                        continue
                    bucket = flagged if any(v in name for v in vocab) else unknown
                    bucket.setdefault(name, (path, lineno))

    print(f"declared names: {len(declared)}    scanned files: {len(sources)}")

    if args.all and unknown:
        print(f"\npresumed external (not flagged) — {len(unknown)}:")
        for name in sorted(unknown):
            path, lineno = unknown[name]
            print(f"  {name}  ({path}:{lineno})")

    core = {n: loc for n, loc in flagged.items() if loc[0] not in frontier}
    front = {n: loc for n, loc in flagged.items() if loc[0] in frontier}

    if args.write_gaps:
        with open(GAPS, "w", encoding="utf-8") as fh:
            fh.write("# Undeclared identifiers referenced by frontier modules: the proof\n")
            fh.write("# obligations that remain to be written.  One per line: name<TAB>file.\n")
            fh.write("# Regenerate with: python3 scripts/check_undefined_names.py --write-gaps\n")
            fh.write("# This list must only ever shrink.  See LEDGER.md.\n")
            for name in sorted(front):
                fh.write(f"{name}\t{front[name][0]}\n")
        print(f"wrote {len(front)} frontier gap(s) to {os.path.relpath(GAPS, ROOT)}")
        return 0

    failed = False

    if core:
        failed = True
        print(f"\n::error::{len(core)} reference(s) to undeclared identifiers in the "
              f"VERIFIED CORE:", file=sys.stderr)
        for name in sorted(core):
            path, lineno = core[name]
            print(f"  {path}:{lineno}: {name}", file=sys.stderr)
        print("\n  Either declare them, or (if they are Mathlib names) add them to\n"
              "  scripts/external_names.txt with a one-line justification.", file=sys.stderr)
    else:
        print("ok: every project-vocabulary identifier referenced from the verified core "
              "is declared")

    # Frontier gaps are expected, but tracked and shrink-only.
    if os.path.exists(GAPS):
        with open(GAPS, encoding="utf-8") as fh:
            base = {ln.split("\t")[0] for ln in fh
                    if ln.strip() and not ln.startswith("#")}
        new = sorted(set(front) - base)
        closed = sorted(base - set(front))
        if new:
            failed = True
            print(f"\n::error::{len(new)} new frontier gap(s) (undeclared identifier in an "
                  f"unverified module):", file=sys.stderr)
            for name in new:
                path, lineno = front[name]
                print(f"  {path}:{lineno}: {name}", file=sys.stderr)
        if closed:
            print(f"note: {len(closed)} frontier gap(s) closed (good); "
                  f"rerun with --write-gaps to shrink the list:")
            for name in closed:
                print(f"  {name}")
        if not new:
            print(f"ok: {len(front)} frontier gap(s), all accounted for")
    else:
        print(f"warning: no frontier-gap baseline ({len(front)} found); "
              f"run --write-gaps", file=sys.stderr)

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

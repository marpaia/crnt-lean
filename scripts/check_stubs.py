#!/usr/bin/env python3
"""Audit for definitions that do not carry their intended mathematical meaning.

Three kinds of hole are invisible to a `sorry` grep and were all present in this
repository at the time this script was written:

  1. `def P (N : Network S) : Prop := True` and variants such as
     `:= ∃ (_ : Unit), True` — every theorem concluding `P` is vacuous.
  2. `structure C (N : Network S) where dummy : True` together with constructors
     returning `⟨trivial⟩` — a "certificate" that carries no information, so a
     proof-producing bridge into it proves nothing.
  3. `instance : Decidable (N.P) := isTrue ...` — makes `decide P = true` a
     theorem for every input, so a decidable analyzer flag is unconditionally on.

The script also enforces the containment rule that matters most in practice: no
module containing a hollow definition may be reachable from the public `CRNT`
umbrella, so `import CRNT` cannot hand a caller a meaningless certificate.

Usage:
    python3 scripts/check_stubs.py              # check against baseline, exit 1 on regression
    python3 scripts/check_stubs.py --write      # rewrite the baseline (review the diff!)
    python3 scripts/check_stubs.py --report     # human-readable listing, always exit 0
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "scripts", "stub_baseline.txt")
UMBRELLA = os.path.join(ROOT, "CRNT.lean")

# Each pattern is (kind, compiled regex).  Patterns are deliberately syntactic and
# conservative: they are meant to have no false negatives on the shapes above, and
# any false positive can be silenced by making the definition non-trivial.
PATTERNS = [
    ("prop-true", re.compile(r":\s*Prop\s*:=\s*True\s*$")),
    ("prop-true", re.compile(r":\s*Prop\s*:=\s*∃\s*\(?_[^,]*,\s*True\s*$")),
    ("prop-true", re.compile(r":\s*Prop\s*:=\s*(?:trivial|Trivial)\s*$")),
    ("dummy-field", re.compile(r"\bdummy\s*:\s*True\b")),
    ("trivial-ctor", re.compile(r":=\s*⟨\s*trivial\s*⟩\s*$")),
    ("trivial-ctor", re.compile(r":=\s*⟨\s*\(\)\s*,\s*trivial\s*⟩\s*$")),
    ("istrue-decider", re.compile(r"Decidable\b.*:=\s*isTrue\b")),
    ("sorry", re.compile(r"(?<!`)\bsorry\b(?!`)")),
    # An `axiom` is the one escape hatch that makes every gate below meaningless: it
    # postulates whatever it likes and every theorem downstream inherits it.  Measured
    # before this pattern existed: `axiom foo : False` added to a module reachable from
    # `CRNT.lean` passed check_stubs, check_exclusions AND check_undefined_names, all
    # exit 0.  There are no `axiom` declarations anywhere in the tree, so this pattern
    # has no false positives to baseline -- and a new one is exactly what should fail.
    ("axiom", re.compile(r"^[\s]*axiom[\s]+[A-Za-z_]")),
    ("admit", re.compile(r"(?<!`)\badmit\b(?!`)")),
]

SCAN_DIRS = ["CRNT", "Scaffold", "test"]
SCAN_FILES = ["CRNT.lean", "Analyze.lean"]


def lean_files() -> list[str]:
    out = []
    for d in SCAN_DIRS:
        for base, _, files in os.walk(os.path.join(ROOT, d)):
            for f in files:
                if f.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(base, f), ROOT))
    for f in SCAN_FILES:
        if os.path.exists(os.path.join(ROOT, f)):
            out.append(f)
    return sorted(out)


def strip_comments(text: str) -> list[str]:
    """Blank out block comments and line comments, preserving line numbering."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    lines = []
    for line in text.split("\n"):
        lines.append(re.sub(r"--.*$", "", line))
    return lines


def findings() -> list[tuple[str, str, int, str]]:
    """Return (kind, path, lineno, text) for every hollow definition found."""
    out = []
    for path in lean_files():
        with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as fh:
            lines = strip_comments(fh.read())
        for i, line in enumerate(lines, start=1):
            for kind, pat in PATTERNS:
                if pat.search(line):
                    out.append((kind, path, i, line.strip()[:120]))
                    break
    return out


def module_of(path: str) -> str:
    return path[:-5].replace(os.sep, ".")


def transitive_imports(entry: str) -> set[str]:
    """Modules reachable from `entry` (a .lean path) by following CRNT imports."""
    seen: set[str] = set()
    stack = [entry]
    imp = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
    while stack:
        path = stack.pop()
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            continue
        with open(full, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for mod in imp.findall(text):
            if mod in seen:
                continue
            seen.add(mod)
            stack.append(mod.replace(".", os.sep) + ".lean")
    return seen


def key(f: tuple[str, str, int, str]) -> str:
    """Baseline key: kind + file + the declaration text, but not the line number.

    Line numbers churn on every edit; the text does not.  This keeps the baseline
    stable under unrelated changes while still pinning what is hollow and where.
    """
    kind, path, _lineno, text = f
    return f"{kind}\t{path}\t{text}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="rewrite the baseline file")
    ap.add_argument("--report", action="store_true", help="print a listing and exit 0")
    args = ap.parse_args()

    found = findings()
    keys = sorted({key(f) for f in found})

    if args.write:
        with open(BASELINE, "w", encoding="utf-8") as fh:
            fh.write("# Hollow/unproved definitions, one per line: kind<TAB>file<TAB>text\n")
            fh.write("# Regenerate with: python3 scripts/check_stubs.py --write\n")
            fh.write("# This list must only ever shrink.  See LEDGER.md.\n")
            for k in keys:
                fh.write(k + "\n")
        print(f"wrote {len(keys)} entries to {os.path.relpath(BASELINE, ROOT)}")
        return 0

    by_kind: dict[str, int] = {}
    for kind, _p, _l, _t in found:
        by_kind[kind] = by_kind.get(kind, 0) + 1

    if args.report:
        print("hollow-definition report")
        print("------------------------")
        for kind in sorted(by_kind):
            print(f"  {kind:16s} {by_kind[kind]}")
        print()
        for kind, path, lineno, text in sorted(found, key=lambda f: (f[1], f[2])):
            print(f"{path}:{lineno}: [{kind}] {text}")
        return 0

    failed = False

    # ---- 1. baseline regression check -------------------------------------
    if not os.path.exists(BASELINE):
        print(f"error: {os.path.relpath(BASELINE, ROOT)} is missing; run --write", file=sys.stderr)
        return 1
    with open(BASELINE, encoding="utf-8") as fh:
        base = {ln.rstrip("\n") for ln in fh if ln.strip() and not ln.startswith("#")}

    new = [k for k in keys if k not in base]
    fixed = [k for k in base if k not in set(keys)]

    if new:
        failed = True
        print(f"::error::{len(new)} new hollow definition(s) introduced:", file=sys.stderr)
        for k in new:
            kind, path, text = k.split("\t", 2)
            print(f"  [{kind}] {path}: {text}", file=sys.stderr)
        print("  If this is intentional, document it in LEDGER.md and rerun with --write.",
              file=sys.stderr)
    if fixed:
        print(f"note: {len(fixed)} baseline entries no longer present (good). "
              f"Run --write to shrink the baseline:")
        for k in fixed:
            kind, path, text = k.split("\t", 2)
            print(f"  [{kind}] {path}: {text}")

    # ---- 2. umbrella containment check ------------------------------------
    stub_modules = {module_of(p) for _k, p, _l, _t in found if p.startswith("CRNT")}
    reachable = transitive_imports("CRNT.lean")
    leaked = sorted(stub_modules & reachable)
    if leaked:
        failed = True
        print("::error::modules with hollow definitions are reachable from `import CRNT`:",
              file=sys.stderr)
        for m in leaked:
            print(f"  {m}", file=sys.stderr)
        print("  Remove them from CRNT.lean, or give the definitions real content.",
              file=sys.stderr)
    else:
        print(f"ok: none of the {len(stub_modules)} module(s) with hollow definitions "
              f"is reachable from `import CRNT`")

    if not failed:
        print(f"ok: {len(keys)} hollow definition(s), all accounted for in the baseline")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

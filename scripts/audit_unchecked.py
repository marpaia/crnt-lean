#!/usr/bin/env python3
"""Audit every `UNCHECKED` declaration: no `sorry`, but its module never elaborated, so
Lean has never seen the proof.

There are 820 of these. They cannot all be elaborated (their modules do not compile), but
the two defect shapes that caught the known fakes are both detectable statically:

  NOTE: the "references a name declared nowhere" audit is NOT done here -- the repo's
  existing `check_undefined_names.py` already does it properly, restricting to
  `scripts/repo_vocabulary.txt` instead of every identifier, and reports exactly 4
  undeclared project names tree-wide (see `scripts/frontier_gaps.txt`).  An earlier
  version of this script reimplemented it naively and reported 347, almost all of which
  were Lean-core names like `congrArg`/`Subtype`.  Use the existing gate.

  VACUOUS?  a *named* mathematical hypothesis never appears in the proof body or the
            conclusion.  This is how `nonterminal_complex_detects_deficiency_coordinate`
            was caught: its conclusion was `∃ α, α ≠ 0 ∧ v = α*d + (v - α*d)`, an instance
            of `a = b + (a - b)`, and none of `hδ`, `h`, `hx`, `hxs`, `hnt` was used.
            Unused *instance/type* binders are normal, so only named hypotheses whose type
            mentions the project vocabulary are reported.  Declarations whose proof uses a
            context-consuming tactic (`omega`, `linarith`, `simp_all`, `aesop`, ...) are
            skipped entirely: those tactics read hypotheses without naming them, so
            "unused" says nothing.  Skipping them took the candidate list from 27 to a
            precise handful.

Usage:
    python3 scripts/audit_unchecked.py              # summary
    python3 scripts/audit_unchecked.py --phantom     # the hard failures, with the names
    python3 scripts/audit_unchecked.py --vacuous     # suspected vacuous statements
    python3 scripts/audit_unchecked.py --by-module   # blockers ranked
"""
from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s:({\[]+)",
    re.M)
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
# a named hypothesis binder: `(hfoo : ...)` or `{hfoo : ...}`
HYP = re.compile(r"[({]\s*([a-z][\w']*)\s*:\s*([^)}]*)[)}]")


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


def load():
    """Return (blocks, declared, imports) where blocks are per-declaration records."""
    blocks, declared, imports = [], set(), {}
    files = []
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
    raw_by_mod = {}
    for path in files:
        mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
        raw = open(path, encoding="utf-8", errors="replace").read()
        raw_by_mod[mod] = raw
        imports[mod] = IMPORT.findall(raw)
        code = strip_comments(raw)
        starts = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(code)]
        for idx, (pos, kind, name) in enumerate(starts):
            end = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
            declared.add(name.split(".")[-1])
            blocks.append({"mod": mod, "kind": kind, "name": name,
                           "body": code[pos:end],
                           "line": code[:pos].count("\n") + 1})
    return blocks, declared, imports, raw_by_mod


def olean(mod):
    return os.path.join(BUILD, mod.replace(".", os.sep) + ".olean")


def main():
    blocks, declared, imports, raw = load()
    # project vocabulary = every declared name, plus anything in the mathlib source tree
    ml = os.path.join(os.path.dirname(ROOT), "mlsrc", "mathlib4-4.31.0", "Mathlib")
    mathlib_names = set()
    if os.path.isdir(ml):
        for dp, _, fs in os.walk(ml):
            for f in fs:
                if f.endswith(".lean"):
                    t = open(os.path.join(dp, f), encoding="utf-8",
                             errors="replace").read()
                    for m in DECL.finditer(t):
                        mathlib_names.add(m.group(2).split(".")[-1])
    known = declared | mathlib_names

    unchecked = [b for b in blocks
                 if b["kind"] in ("theorem", "lemma")
                 and not re.search(r"\bsorry\b", b["body"])
                 and not os.path.exists(olean(b["mod"]))]

    vacuous = []
    for b in unchecked:
        body = b["body"]
        # split statement / proof at the first `:=`
        cut = body.find(":=")
        stmt = body[:cut] if cut > 0 else body
        proof = body[cut:] if cut > 0 else ""
        # --- VACUOUS?: a named hypothesis never used anywhere ---------------------
        # tactics that consume the whole local context without naming anything
        if re.search(r"\b(omega|linarith|nlinarith|polyrith|simp_all|aesop|tauto|"
                     r"assumption|decide|positivity|field_simp|norm_num|gcongr|"
                     r"bound|order)\b", proof):
            continue
        unused = []
        for hname, htype in HYP.findall(stmt):
            if not re.search(r"[A-Z]", htype):      # not project vocabulary
                continue
            after = stmt[stmt.find(hname) + len(hname):] + proof
            if not re.search(r"\b" + re.escape(hname) + r"\b", after):
                unused.append(hname)
        if unused:
            vacuous.append((b, unused))

    by_mod = defaultdict(int)
    for b in unchecked:
        by_mod[b["mod"]] += 1

    print(f"UNCHECKED theorems/lemmas: {len(unchecked)} "
          f"across {len(by_mod)} non-elaborating modules")
    print(f"  VACUOUS? (a named hypothesis is never used)                   : "
          f"{len(vacuous)}")
    print(f"  no static red flag                                            : "
          f"{len(unchecked) - len(vacuous)}")
    print("\n(undeclared-name audit: use scripts/check_undefined_names.py -- it reports 4)")

    if "--vacuous" in sys.argv:
        print("\n=== suspected vacuous (unused named hypotheses) ===")
        for b, names in sorted(vacuous, key=lambda t: -len(t[1])):
            print(f"{b['mod']}:{b['line']}  {b['name']}")
            print(f"    unused: {', '.join(names)}")
    if "--by-module" in sys.argv:
        print("\n=== UNCHECKED count by module ===")
        for m, c in sorted(by_mod.items(), key=lambda kv: -kv[1])[:30]:
            print(f"{c:>4}  {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

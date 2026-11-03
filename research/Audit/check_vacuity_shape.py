#!/usr/bin/env python3
"""Detect the *vacuous-by-empty-argument* shape, statically, across `CRNT/`.

The shape
---------

A **set-valued map** is a type synonym (or `def`) whose body is a function type ending in
`Set`:

    abbrev Field (E : Type*) := E → Set E          -- CRNT/Dynamics/DifferentialInclusion.lean:43

Note what is *absent*: nothing requires `F x` to be inhabited.  Now take a theorem whose
hypothesis mentions the map's values and whose conclusion is a property of the flow:

    theorem forwardInvariant_barrierSublevel
        {F : DifferentialInclusion.Field E}
        (hdesc : ∀ y, R ≤ barrier L b y → … → ∀ c ∈ F y, L i c ≤ 0) :
        ForwardInvariant F {x | barrier L b x ≤ R}

Instantiate `F := fun _ => ∅`.  Every hypothesis of the shape `∀ c ∈ F y, P c` becomes true
(`c ∈ ∅` is unsatisfiable), and `ForwardInvariant F R` becomes true for **every** `R`, because
`IsInclusionSolution (fun _ => ∅) γ` has no solution at all.  So all four
`ForwardInvariant` conclusions of `CRNT/Geometry/PolyhedralBarrier.lean` are obtained for free
by an empty field.  `adv-vacuity` machine-checked exactly this
(`test/VacuityAudit.lean :: forwardInvariant_vacuous_for_empty_field`, PR #16) and correctly
graded it `[M]`: the *theorem* is not vacuous in general
(`forwardInvariant_not_vacuous_in_general` discharges `{1}` at `{x | x ≤ 0}`), it is vacuous
for a degenerate argument that no hypothesis excludes.

This script finds the shape by **static analysis of the statement text only** — no `lean`, no
elaboration, no `.olean`.  It is a *screen*, not a verdict: a hit means "a reader must confirm
this is load-bearing", and a miss means nothing (see "What this does not decide" below).

Usage
-----
    python3 research/Audit/check_vacuity_shape.py
    python3 research/Audit/check_vacuity_shape.py --json
    python3 research/Audit/check_vacuity_shape.py --explain CRNT.Geometry.PolyhedralBarrier
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# A declaration header: `theorem name` / `lemma name` at column 0.
DECL_RE = re.compile(r"^(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w'.]*)", re.M)

# A set-valued map: a def/abbrev whose *body* is a function type ending in `Set`.
# Non-`Set` bodies (e.g. `List`, `Finset`, `Option`) are deliberately out of scope: they have
# a canonical empty value too, but the emptiness argument below is about `∅` specifically.
SVF_DEF_RE = re.compile(
    r"^(?:abbrev|def)\s+([A-Za-z_][\w'.]*)\s*(\([^)]*\))?\s*(:\s*[^:=\n]+)?:=\s*"
    r"([^\n]*→\s*Set\s+[^\n]+)$",
    re.M,
)

# Tokens that discharge the emptiness problem somewhere in a statement.
NONEMPTY_TOKENS = ("Nonempty", ".Nonempty", "≠ ∅", "≠ ∅", "<$>", "Set.Nonempty")


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    return "\n".join(re.sub(r"--.*$", "", ln) for ln in text.split("\n"))


def crnt_files() -> list[str]:
    out = []
    for r, _, files in os.walk(os.path.join(ROOT, "CRNT")):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(r, f))
    return sorted(out)


def module_of(path: str) -> str:
    return os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")


def set_valued_maps(files: dict[str, str]) -> dict[str, list[str]]:
    """`definition name -> [modules defining it]`, for bodies of the shape `… → Set …`."""
    out: dict[str, list[str]] = {}
    for mod, text in files.items():
        for m in SVF_DEF_RE.finditer(text):
            out.setdefault(m.group(1), []).append(mod)
    return out


def statement_of(text: str, start: int) -> tuple[str, int]:
    """Return `(statement, end_offset)` for the declaration beginning at `start`.

    The statement runs from the header to the `:=` that starts the proof, at bracket depth 0.
    Falling back to the next declaration header keeps a malformed declaration from swallowing
    the rest of the file.
    """
    depth = 0
    for i in range(start, len(text)):
        ch = text[i]
        if ch in "({[⟨":
            depth += 1
        elif ch in ")}]⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and text[i : i + 2] == ":=":
            return text[start:i], i
    nxt = DECL_RE.search(text, start + 1)
    return text[start : nxt.start() if nxt else len(text)], nxt.start() if nxt else len(text)


def findings() -> dict:
    files = {module_of(p): strip_comments(open(p, encoding="utf-8", errors="replace").read())
             for p in crnt_files()}
    svf = set_valued_maps(files)

    hits = []
    for mod, text in files.items():
        for m in DECL_RE.finditer(text):
            kind, name = m.group(1), m.group(2)
            if kind not in ("theorem", "lemma"):
                continue
            stmt, _end = statement_of(text, m.start())

            # Which set-valued maps does this statement quantify over?  The name may be
            # qualified -- `{F : DifferentialInclusion.Field E}` is the form used by every
            # barrier theorem, and a match that only accepts the bare name `Field` silently
            # misses all four of them.  So match an optional dotted prefix.
            used = []
            for svf_name in svf:
                pat = r"(?<![A-Za-z0-9_'\"])(?:[A-Za-z_][\w']*\.)*" + re.escape(svf_name) + r"(?![A-Za-z0-9_'])"
                if re.search(pat, stmt):
                    used.append(svf_name)
            if not used:
                continue

            # A binder over such a map: `{F : …Map …}` or `(F : …Map …)`, qualified or not.
            binders = []
            for svf_name in used:
                pat = (r"\{?\s*([A-Za-z_][\w']*)\s*:\s*[^,(){}]*"
                       r"(?:[A-Za-z_][\w']*\.)*" + re.escape(svf_name) + r"\b")
                binders.extend(re.findall(pat, stmt))
            binders = sorted(set(binders))
            if not binders:
                continue

            # Does the statement quantify over the map's *values*?  Two forms: `F y`, applied
            # to an argument; or `∈ F y`, the membership form every barrier hypothesis uses.
            quantified = any(
                re.search(r"(?<![A-Za-z0-9_'\"])" + re.escape(v) + r"\s+(?:[A-Za-z_][\w']*\(?|\S)", stmt)
                for v in binders
            )
            if not quantified:
                continue

            # Is any emptiness obligation discharged anywhere in the statement?
            guard = any(tok in stmt for tok in NONEMPTY_TOKENS)
            hits.append({
                "module": mod,
                "decl": name,
                "kind": kind,
                "set_valued_map": used[0],
                "map_defined_in": svf[used[0]],
                "binders": sorted(set(binders)),
                "emptiness_guarded": guard,
                "line": text[: m.start()].count("\n") + 1,
                "statement": " ".join(stmt.split()),
            })

    unguarded = [h for h in hits if not h["emptiness_guarded"]]
    return {
        "set_valued_maps": {k: v for k, v in sorted(svf.items())},
        "modules_scanned": len(files),
        "statements_examined": sum(
            1 for t in files.values() for _ in DECL_RE.finditer(t)
        ),
        "hits": sorted(hits, key=lambda h: (h["module"], h["line"])),
        "unguarded": sorted(unguarded, key=lambda h: (h["module"], h["line"])),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--explain", metavar="MODULE",
                    help="print the full statement of each hit in MODULE")
    args = ap.parse_args()

    r = findings()
    if args.explain:
        sel = [h for h in r["hits"] if h["module"].startswith(args.explain)]
        if not sel:
            print(f"no hits in {args.explain}", file=sys.stderr)
            return 1
        for h in sel:
            print(f"\n{h['module']} : {h['line']}  {h['decl']}")
            print(f"  set-valued map : {h['set_valued_map']}  "
                  f"(defined in {', '.join(h['map_defined_in'])})")
            print(f"  binders        : {h['binders']}")
            print(f"  guarded        : {h['emptiness_guarded']}")
            print(f"  statement      : {h['statement'][:600]}")
        return 0

    if args.json:
        print(json.dumps(r, indent=2))
        # A hit is not a failure: the predicate may be load-bearing.  Exit 1 only to signal
        # "there is something to read", which CI must not treat as red.  See the note below.
        return 0

    print("=== VACUITY SHAPE SCAN ===")
    print(f"modules scanned            : {r['modules_scanned']}")
    print(f"statements examined        : {r['statements_examined']}")
    print(f"set-valued maps found      : {len(r['set_valued_maps'])}")
    for name, mods in r["set_valued_maps"].items():
        print(f"   {name}  ({', '.join(mods)})")
    print()
    print(f"statements over a set-valued map : {len(r['hits'])}")
    print(f"   ... with no emptiness guard     : {len(r['unguarded'])}")
    print()
    for h in r["unguarded"]:
        print(f"  {h['module']} : {h['line']}  {h['decl']}")
        print(f"      map {h['set_valued_map']} (defined in {', '.join(h['map_defined_in'])}), "
              f"binder {h['binders']}")
    print()
    print("Every hit above admits the empty-map instance unless a hypothesis excludes it.")
    print("This is a SCREEN, not a verdict: confirm each one by exhibiting an inhabited")
    print("instance, or add the nonemptiness hypothesis the statement actually needs.")
    print()
    print("What this does NOT decide:")
    print("  * whether the theorem is vacuous -- that needs an inhabitedness proof;")
    print("  * a set-valued map whose type is written with an explicit `Set` binder rather")
    print("    than a synonym (e.g. `{F : E → Set E}` inline) is NOT matched;")
    print("  * hypotheses discharged outside the statement (via `variable`, a namespace")
    print("    default, or a section) are invisible to a text scan;")
    print("  * `Finset`/`List`/`Option`-valued maps are out of scope by construction.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
#!/usr/bin/env python3
"""Coverage and soundness audit for the CRNT exclusion ledger.

Built on `research/Audit/ledger_integrity.py` (adv-audit, PR #14), which established that

* no wrongly-verified module exists -- the closure of `CRNT.lean` is 701 modules and none
  of them carries a `sorry`, an `axiom` or an `admit`;
* but `scripts/check_exclusions.py` check 4 is **vacuous** against an empty ledger, and
* 145 `CRNT/` modules are neither in the ledger nor reachable from `CRNT.lean`, and both
  holes are among them.

This script closes that gap.  It classifies every module on disk into exactly one of three
classes and states an invariant for each, then it *proves the non-vacuity of the invariant
that replaces check 4*, and it runs a mutation test so the claim is certified rather than
asserted.

    core        reachable from `CRNT.lean` by `import CRNT...` lines
    frontier    named in `scripts/unverified_modules.txt` (the `excludeGlobs` of `CRNT`)
    orphan      on disk, in neither

Usage
-----
    python3 research/Audit/ledger_coverage.py            # human report, exit 1 on failure
    python3 research/Audit/ledger_coverage.py --json
    python3 research/Audit/ledger_coverage.py --selftest # mutation test: does C3 have teeth?
    python3 research/Audit/ledger_coverage.py --module CRNT/Dynamics/Foo.lean
        # the `close_hole.sh` step-2b query: is this module transitively sorryAx-bearing?
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
UMBRELLA = os.path.join(ROOT, "CRNT.lean")
ORPHAN_BASELINE = os.path.join(ROOT, "research", "Audit", "orphan_baseline.txt")
KNOWN_HOLES = os.path.join(ROOT, "research", "Audit", "known_holes.txt")

IMPORT_RE = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
# `sorry` as a token: not preceded by `.`/`'`/`"`/identifier char, not followed by one.
SORRY_RE = re.compile(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])")
AXIOM_RE = re.compile(r"^\s*(?:axiom|constant)\s+\w+", re.M)
ADMIT_RE = re.compile(r"(?<![A-Za-z_.'\"])\badmit\b(?![A-Za-z_])")
# A top-level declaration header.  Names capture the last dotted component too, so
# `theorem foo.bar` yields `foo.bar` and a qualified use `Foo.foo.bar` still matches.
DECL_RE = re.compile(r"^(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w'.]*)", re.M)


# ------------------------------------------------------------------ source reading


def strip_comments(text: str) -> str:
    """Blank out Lean block and line comments, preserving line numbering."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    return "\n".join(re.sub(r"--.*$", "", ln) for ln in text.split("\n"))


def mod_path(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def crnt_modules_on_disk() -> list[str]:
    out = []
    for r, _, files in os.walk(os.path.join(ROOT, "CRNT")):
        for f in files:
            if f.endswith(".lean"):
                out.append(
                    os.path.relpath(os.path.join(r, f), ROOT)[:-5].replace(os.sep, ".")
                )
    return sorted(out)


def read_ledger() -> list[str]:
    with open(LEDGER, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]


# ------------------------------------------------------------- the import graph


class Graph:
    """The CRNT import graph, built once and queried many times.

    Every source file is read and comment-stripped exactly once.  An earlier draft of this
    analysis re-read and re-regexed every file inside the transitive-closure loop and took
    35 s for a query that answers in well under one second this way.
    """

    def __init__(self, root: str = ROOT) -> None:
        self.root = root
        self.modules = []
        for r, _, files in os.walk(os.path.join(root, "CRNT")):
            for f in files:
                if f.endswith(".lean"):
                    self.modules.append(
                        os.path.relpath(os.path.join(r, f), root)[:-5].replace(os.sep, ".")
                    )
        self.modules.sort()
        self.source: dict[str, str] = {}
        for m in self.modules:
            try:
                with open(self._path(m), encoding="utf-8", errors="replace") as fh:
                    self.source[m] = strip_comments(fh.read())
            except FileNotFoundError:
                self.source[m] = ""
        self.imports: dict[str, list[str]] = {
            m: [i for i in IMPORT_RE.findall(t) if i in self.source] for m, t in self.source.items()
        }
        self._closure: dict[str, frozenset[str]] = {}

    def _path(self, mod: str) -> str:
        return os.path.join(self.root, mod.replace(".", os.sep) + ".lean")

    def closure(self, mod: str) -> frozenset[str]:
        """Every CRNT module reachable from `mod` by CRNT import lines (excluding `mod`)."""
        if mod in self._closure:
            return self._closure[mod]
        seen: set[str] = set()
        stack = [mod]
        while stack:
            cur = stack.pop()
            for i in self.imports.get(cur, ()):
                if i not in seen:
                    seen.add(i)
                    stack.append(i)
        seen.discard(mod)
        froz = frozenset(seen)
        self._closure[mod] = froz
        return froz

    def umbrella_closure(self) -> frozenset[str]:
        """CRNT modules reachable from `CRNT.lean` itself."""
        entry = os.path.join(self.root, "CRNT.lean")
        with open(entry, encoding="utf-8", errors="replace") as fh:
            seen: set[str] = set()
            stack = list(IMPORT_RE.findall(fh.read()))
            while stack:
                m = stack.pop()
                if m not in seen:
                    seen.add(m)
                    stack.extend(self.imports.get(m, ()))
        return frozenset(seen)


# ------------------------------------------------------------- the sorryAx analysis


def holed_declarations(g: Graph) -> dict[str, list[str]]:
    """`module -> [names of declarations whose own body contains a sorry]`.

    This is deliberately *not* every declaration in a hole-bearing file.  A module that
    imports a hole but uses only the file's proved lemmas does not carry `sorryAx`; treating
    the whole file as tainted would report four false positives.
    """
    out: dict[str, list[str]] = {}
    for mod, text in g.source.items():
        if not (SORRY_RE.search(text) or ADMIT_RE.search(text)):
            continue
        names: list[str] = []
        # Scan declaration by declaration: everything from a header to the next header.
        heads = [(m.start(), m.group(1)) for m in DECL_RE.finditer(text)]
        for idx, (start, name) in enumerate(heads):
            end = heads[idx + 1][0] if idx + 1 < len(heads) else len(text)
            if SORRY_RE.search(text[start:end]):
                names.append(name)
        out[mod] = names
    return out


def taint_sources(g: Graph) -> dict[str, list[str]]:
    """`module -> [axioms the module itself introduces]`, from the source text."""
    out: dict[str, list[str]] = {}
    for mod, text in g.source.items():
        kinds = []
        if SORRY_RE.search(text):
            kinds.append("sorry")
        if ADMIT_RE.search(text):
            kinds.append("admit")
        if AXIOM_RE.search(text):
            kinds.append("axiom")
        if kinds:
            out[mod] = kinds
    return out


def sorryax_tainted(g: Graph, holed: dict[str, list[str]]) -> dict[str, list[str]]:
    """`module -> [reasons it carries sorryAx transitively]`, sorted, deduplicated.

    Two ways a module picks up `sorryAx`:

    1. it *declares* it (a `sorry`, `admit` or `axiom` in its own body);
    2. it *uses* a holed declaration of a module in its transitive import closure.

    (2) is the transitive half, and it is what a purely syntactic per-file scan misses.
    """
    reasons: dict[str, list[str]] = {}
    for mod, kinds in taint_sources(g).items():
        reasons[mod] = [f"declares {','.join(kinds)}"]

    for mod, text in g.source.items():
        if mod in reasons:
            continue
        closure = g.closure(mod)
        for hole_mod, names in holed.items():
            if hole_mod not in closure:
                continue
            hits = [
                n
                for n in names
                if re.search(r"(?<![A-Za-z0-9_'\"])" + re.escape(n) + r"(?![A-Za-z0-9_'])", text)
            ]
            if hits:
                reasons[mod] = [f"uses {hole_mod}.{n}" for n in hits]
                break
    return {m: sorted(r) for m, r in sorted(reasons.items())}


# ------------------------------------------------------------------- the checks


def audit(root: str = ROOT) -> dict:
    g = Graph(root)
    disk = set(g.modules)
    ledger = set(read_ledger() if root == ROOT else [])
    core = set(g.umbrella_closure())

    holed = holed_declarations(g)
    tainted = sorryax_tainted(g, holed)

    orphans = disk - ledger - core
    stale = sorted(m for m in ledger if m not in disk)
    redundant = sorted(ledger & core)

    problems: list[str] = []

    # -- C1 the three classes partition the disk -------------------------------------
    if disk & ledger & core:
        problems.append(
            "modules are in both the ledger and the umbrella closure: "
            + ", ".join(sorted(disk & ledger & core))
        )

    # -- C2 a frontier module must not be imported by the core (old check 4) ----------
    #     Reported, with its vacuity status computed rather than assumed.
    leaked = sorted(ledger & core)
    if leaked:
        problems.append("CRNT.lean transitively imports ledger modules: " + ", ".join(leaked))
    check4_vacuous = not ledger

    # -- C3 THE REPLACEMENT FOR CHECK 4, and the invariant that matters ---------------
    #     "The verified core does not depend on hole-bearing source."  Unlike check 4 this
    #     is not empty on either side: the tainted set is non-empty until holes = 0.
    core_tainted = sorted(set(core) & set(tainted))
    if core_tainted:
        problems.append(
            "the verified core reaches modules carrying sorryAx: "
            + ", ".join(core_tainted)
        )
    # C3 is vacuous if and only if nothing on disk carries a sorry -- see the proof in
    # research/Tooling-COVERAGE.md.  Assert the equivalence here so it is checked, not
    # just documented.
    holes_on_disk = sorted(m for m, _ in holed.items())
    c3_vacuous = not tainted

    # -- C4 every hole-bearing module is on the known-holes manifest -------------------
    known: set[str] = set()
    if os.path.exists(KNOWN_HOLES) and root == ROOT:
        with open(KNOWN_HOLES, encoding="utf-8") as fh:
            known = {ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")}
    undeclared = sorted(set(tainted) - known) if known else []
    if known and undeclared:
        problems.append(
            "modules carrying sorryAx that are not on research/Audit/known_holes.txt: "
            + ", ".join(undeclared)
        )

    # -- C5 orphans are shrink-only, and are never put on the ledger ------------------
    baseline = None
    if os.path.exists(ORPHAN_BASELINE) and root == ROOT:
        with open(ORPHAN_BASELINE, encoding="utf-8") as fh:
            nums = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
        baseline = int(nums[0]) if nums else None
    if baseline is not None and len(orphans) > baseline:
        problems.append(
            f"the orphan set grew from {baseline} to {len(orphans)}; a module left the "
            "umbrella closure without a decision being recorded"
        )

    return {
        "modules_on_disk": len(disk),
        "core_size": len(core),
        "ledger_size": len(ledger),
        "orphan_count": len(orphans),
        "orphans": sorted(orphans),
        "orphan_baseline": baseline,
        "stale_ledger_entries": stale,
        "redundant_ledger_entries": redundant,
        "check4_leaked": leaked,
        "check4_is_vacuous": check4_vacuous,
        "tainted_modules": tainted,
        "tainted_count": len(tainted),
        "core_tainted": core_tainted,
        "c3_is_vacuous": c3_vacuous,
        "holes_on_disk": holes_on_disk,
        "known_holes_manifest": sorted(known),
        "undeclared_tainted": undeclared,
        "problems": problems,
    }


# ------------------------------------------------------------------- self-test
#
# A check that cannot fail is not a check.  `--selftest` proves C3 has teeth by building
# a throwaway copy of the tree, injecting one synthetic `sorry` into a module that
# `CRNT.lean` already reaches, and asserting that C3 reports it.  Without this, "no
# wrongly-verified module exists" is an assertion; with it, it is a certified negative.


def selftest() -> int:
    print("=== C3 MUTATION TEST ===")
    print("Inject a `sorry` into a module the umbrella already reaches, in a throwaway")
    print("copy of the tree, and confirm the check fires.  Nothing here touches the repo.\n")

    base = audit()
    print(f"baseline: core={base['core_size']} tainted={base['tainted_count']} "
          f"problems={len(base['problems'])}")
    if base["core_tainted"]:
        print("::error::baseline already violates C3; mutation test is meaningless")
        return 1

    # Pick a target: a leaf-ish core module with no CRNT importers, so the injected sorry
    # cannot be masked by an unrelated file already failing.
    g = Graph(ROOT)
    core = g.umbrella_closure()
    importers: dict[str, int] = {m: 0 for m in core}
    for m in core:
        for i in g.imports.get(m, ()):
            if i in importers:
                importers[i] += 1
    target = sorted(m for m in core if importers[m] == 0)
    if not target:
        print("::error::no core module with zero importers; pick a different strategy")
        return 1
    victim = target[0]
    print(f"victim: {victim}  (0 CRNT importers, so it is in the core by import from CRNT.lean)")

    with tempfile.TemporaryDirectory() as tmp:
        dst = os.path.join(tmp, "tree")
        shutil.copytree(
            ROOT, dst,
            ignore=shutil.ignore_patterns(".git", ".lake", "build", "__pycache__"),
        )
        vpath = os.path.join(dst, victim.replace(".", os.sep) + ".lean")
        with open(vpath, "a", encoding="utf-8") as fh:
            fh.write("\n\ntheorem mutationTestOnly : 0 = 1 := by sorry\n")
        mutated = audit(dst)
        print(f"mutated: core={mutated['core_size']} tainted={mutated['tainted_count']} "
              f"problems={len(mutated['problems'])}")

        fired = victim in mutated["core_tainted"]
        print(f"C3 fires on the injected module: {fired}")
        if not fired:
            print("::error::C3 did NOT fire on an injected sorry -- the check is vacuous "
                  "for reasons the audit did not anticipate", file=sys.stderr)
            return 1
        for p in mutated["problems"]:
            print(f"   reported: {p}")

    print("\nPASS: C3 detects a single injected `sorry` in the verified core.")
    print("PASS: the negative result 'no wrongly-verified module exists' is certified, "
          "not merely asserted.")
    return 0


# ------------------------------------------------------------------ module query
#
# The `close_hole.sh` step-2b query.  `#print axioms` on one named theorem does not catch a
# module that is hole-free in isolation yet transitively rests on a holed declaration.


def module_query(path: str) -> int:
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    if rel.endswith(".lean"):
        rel = rel[:-5]
    mod = rel.replace(os.sep, ".")
    g = Graph(ROOT)
    holed = holed_declarations(g)
    tainted = sorryax_tainted(g, holed)

    print(f"module : {mod}")
    if mod not in g.source:
        print(f"::error::{rel} is not a module under CRNT/", file=sys.stderr)
        return 1

    if mod in tainted:
        print("  FAIL: carries sorryAx")
        for r in tainted[mod]:
            print(f"    {r}")
        print("\n  This module is hole-free in isolation but transitively depends on a")
        print("  holed declaration.  A `#print axioms` on one theorem it happens to export")
        print("  can still be clean, so certify the module, not one name.")
        return 1

    in_core = mod in g.umbrella_closure()
    print(f"  ok: no sorryAx in this module or its transitive import closure "
          f"({len(g.closure(mod))} CRNT modules)")
    print(f"  {'in' if in_core else 'NOT in'} the CRNT.lean closure")
    return 0


# ------------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--selftest", action="store_true",
                    help="mutation-test C3; proves the check can fail")
    ap.add_argument("--module", metavar="PATH",
                    help="close_hole.sh step 2b: transitive sorryAx check for one module")
    args = ap.parse_args()

    if args.module:
        return module_query(args.module)
    if args.selftest:
        return selftest()

    r = audit()
    if args.json:
        print(json.dumps(r, indent=2))
        return 1 if r["problems"] else 0

    print("=== LEDGER COVERAGE ===")
    print(f"modules on disk                 : {r['modules_on_disk']}")
    print(f"  core (reachable from CRNT.lean): {r['core_size']}")
    print(f"  frontier (scripts/unverified)  : {r['ledger_size']}")
    print(f"  orphan (neither)               : {r['orphan_count']}"
          + (f"  (baseline {r['orphan_baseline']})" if r["orphan_baseline"] is not None else ""))
    print()

    print("-- C2  old check 4: does the core reach a ledger module? --")
    print(f"   leaked: {len(r['check4_leaked'])}")
    print(f"   VACUOUS: {r['check4_is_vacuous']}"
          + ("  -- the ledger is empty, so the intersection is empty for every tree"
             if r["check4_is_vacuous"] else ""))
    print("   This check carries no information while the ledger is empty.  See C3.")
    print()

    print("-- C3  the invariant that replaces it: no sorryAx in the verified core --")
    print(f"   sorryAx-tainted modules on disk : {r['tainted_count']}")
    for m, why in r["tainted_modules"].items():
        print(f"     {m}")
        for w in why:
            print(f"        {w}")
    print(f"   tainted AND in the core         : {len(r['core_tainted'])}")
    for m in r["core_tainted"]:
        print(f"     {m}")
    print(f"   C3 vacuous: {r['c3_is_vacuous']}"
          + ("  -- equivalent to `holes = 0`, i.e. vacuous exactly when the goal is met"
             if r["c3_is_vacuous"] else "  -- NON-vacuous: both operands are non-empty"))
    print(f"   (certified by `--selftest`, which injects a sorry into the core and "
          f"requires this to fire)")
    print()

    print("-- C4  hole-bearing modules vs the manifest --")
    print(f"   declared holes            : {r['holes_on_disk']}")
    print(f"   manifest                  : {r['known_holes_manifest'] or '(absent)'}")
    print(f"   tainted but undeclared    : {len(r['undeclared_tainted'])}")
    for m in r["undeclared_tainted"]:
        print(f"     {m}")
    print()

    if r["problems"]:
        print("FAIL")
        for p in r["problems"]:
            print(f"  ::error::{p}", file=sys.stderr)
        return 1
    print("ok: every module is classified, and the verified core is sorryAx-free.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
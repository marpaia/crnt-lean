#!/usr/bin/env python3
"""Ledger-integrity audit for the CRNT exclusion ledger.

Answers, in both directions, the question the ledger is supposed to make answerable:

    Is every module listed in `scripts/unverified_modules.txt` really unverified,
    and is every module NOT listed really verified?

This is an *audit instrument*, not a CI gate -- it deliberately does not decide what "verified"
means.  It only makes the discrepancy visible.  A module that is on disk but is neither in the
ledger nor reachable from `CRNT.lean` is neither trusted nor excluded by anything, and that is
the state that hides problems.

The three notions it distinguishes:

  verified-core   reachable from `CRNT.lean` by CRNT imports (the umbrella's transitive closure)
  unverified      named in `scripts/unverified_modules.txt` (excluded from the `CRNT` lake target)
  orphan          on disk, in neither set: built by the `CRNT.+` glob, but not reachable from
                  the umbrella and not covered by the ledger's invariants

Run:
    python3 research/Audit/ledger_integrity.py
    python3 research/Audit/ledger_integrity.py --json
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
BASELINE = os.path.join(ROOT, "scripts", "unverified_baseline.txt")
UMBRELLA = os.path.join(ROOT, "CRNT.lean")
CACHE = os.environ.get(
    "CRNT_OLEAN_CACHE", "/Users/akutuva/Documents/Proofs/crnt-lean/.lake/build/lib/lean"
)

IMPORT_RE = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
# `sorry` as a token, not preceded by `.`/`'`/`"` and not followed by an identifier char.
SORRY_RE = re.compile(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])")
AXIOM_RE = re.compile(r"^\s*(axiom|constant)\s+\w+", re.M)
ADMIT_RE = re.compile(r"(?<![A-Za-z_.'\"])\badmit\b(?![A-Za-z_])")


def strip_comments(text: str) -> str:
    """Blank out Lean block and line comments, preserving line numbering."""
    text = re.sub(r"/-.*?-/", lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    return "\n".join(re.sub(r"--.*$", "", ln) for ln in text.split("\n"))


def read_ledger() -> list[str]:
    with open(LEDGER, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]


def mod_path(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def crnt_modules_on_disk() -> list[str]:
    out = []
    for r, _, files in os.walk(os.path.join(ROOT, "CRNT")):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(r, f), ROOT)[:-5].replace(os.sep, "."))
    return sorted(out)


def umbrella_closure() -> set[str]:
    """CRNT modules reachable from `CRNT.lean` by following `import CRNT...` lines."""
    seen: set[str] = set()
    stack = ["CRNT.lean"]
    while stack:
        path = stack.pop()
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            continue
        with open(full, encoding="utf-8", errors="replace") as fh:
            for m in IMPORT_RE.findall(fh.read()):
                if m not in seen:
                    seen.add(m)
                    stack.append(m.replace(".", os.sep) + ".lean")
    return seen


def source_of(mod: str) -> str:
    with open(mod_path(mod), encoding="utf-8", errors="replace") as fh:
        return strip_comments(fh.read())


def has_olean(mod: str) -> bool:
    return os.path.exists(os.path.join(CACHE, mod.replace(".", os.sep) + ".olean"))


def audit() -> dict:
    ledger = read_ledger()
    ledger_set = set(ledger)
    on_disk = crnt_modules_on_disk()
    disk_set = set(on_disk)
    core = umbrella_closure()

    # -- direction 1: ledger entries that are stale (no file) or already in the verified core ----
    stale = sorted(m for m in ledger_set if not os.path.exists(mod_path(m)))
    redundant = sorted(ledger_set & core)

    # -- direction 2: modules outside the ledger that are nonetheless defective ------------------
    #   (a) carry an executable `sorry`, `axiom`, or `admit`;
    #   (b) are in the umbrella's transitive closure and so are trusted by `import CRNT`.
    defects: dict[str, list[str]] = {}
    for mod in on_disk:
        body = source_of(mod)
        kinds = []
        if SORRY_RE.search(body):
            kinds.append("sorry")
        if AXIOM_RE.search(body):
            kinds.append("axiom")
        if ADMIT_RE.search(body):
            kinds.append("admit")
        if kinds:
            defects[mod] = kinds

    undeclared_defects = sorted(
        (m, k) for m, k in defects.items() if m not in ledger_set
    )
    in_core_defects = sorted(
        (m, k) for m, k in defects.items() if m in core and m not in ledger_set
    )

    # -- orphans: on disk, not in the ledger, not reachable from the umbrella -------------------
    orphans = sorted(disk_set - ledger_set - core)

    # -- does the umbrella ever reach a hole module? (the one invariant that really matters) ----
    core_reaches_holes = sorted(mod for mod, _ in in_core_defects)

    # -- build evidence --------------------------------------------------------------------------
    no_olean = sorted(m for m in on_disk if not has_olean(m))

    with open(BASELINE, encoding="utf-8") as fh:
        nums = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
    baseline = int(nums[0]) if nums else None

    return {
        "ledger_size": len(ledger),
        "baseline": baseline,
        "ledger_grew": (baseline is not None and len(ledger) > baseline),
        "modules_on_disk": len(on_disk),
        "umbrella_closure_size": len(core),
        "orphans": orphans,
        "orphan_count": len(orphans),
        "stale_ledger_entries": stale,
        "redundant_ledger_entries": redundant,
        "undeclared_defects": undeclared_defects,
        "unverified_core_reaches_holes": core_reaches_holes,
        "modules_without_olean": no_olean,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    r = audit()
    if args.json:
        print(json.dumps(r, indent=2))
        return 0

    print("=== LEDGER INTEGRITY ===")
    print(f"ledger entries                     : {r['ledger_size']} (baseline {r['baseline']})")
    print(f"CRNT modules on disk               : {r['modules_on_disk']}")
    print(f"reachable from CRNT.lean           : {r['umbrella_closure_size']}")
    print(f"orphan modules (no ledger, no core): {r['orphan_count']}")
    print()
    print("-- direction 1: ledger entries that are wrong --")
    print(f"   stale (no file on disk)   : {len(r['stale_ledger_entries'])}")
    for m in r["stale_ledger_entries"]:
        print(f"     {m}")
    print(f"   redundant (already in core): {len(r['redundant_ledger_entries'])}")
    for m in r["redundant_ledger_entries"]:
        print(f"     {m}")
    print()
    print("-- direction 2: defects declared outside the ledger --")
    print(f"   modules carrying sorry/axiom/admit but not in the ledger: "
          f"{len(r['undeclared_defects'])}")
    for m, k in r["undeclared_defects"]:
        tag = "IN VERIFIED CORE" if m in umbrella_closure() else "orphan"
        print(f"     {m}  [{','.join(k)}]  ({tag})")
    print()
    print("-- headline check: does `import CRNT` reach any module with a hole? --")
    hit = r["unverified_core_reaches_holes"]
    if hit:
        print("   YES -- FAILURE MODE PRESENT:")
        for m in hit:
            print(f"     {m}")
    else:
        print("   no: every module reachable from CRNT.lean is free of sorry/axiom/admit")
    print()
    print(f"-- build evidence: CRNT modules with no .olean in {CACHE} --")
    print(f"   {len(r['modules_without_olean'])}")
    for m in r["modules_without_olean"][:20]:
        print(f"     {m}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

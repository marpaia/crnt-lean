#!/usr/bin/env python3
"""Fail if any `import CRNT...` names a module with no file on disk.

This is the cheapest of all the static gates and it has no false positives, because a
missing internal module is a fact about the filesystem rather than a guess about
Mathlib.  It matters because the failure is otherwise completely silent: a module that
imports a nonexistent module is simply excluded from the build and nobody notices.

Three such imports existed when this script was written:

    CRNT.Dynamics.FlowSmoothDependence   <- Oscillation/FloquetOrbitalStability.lean:4
                                            Oscillation/PlanarFlowRegularity.lean:3
    CRNT.Oscillation.ReturnMapContraction <- Oscillation/FloquetOrbitalStability.lean:3
    CRNT.Decision.StrictConeRealization   <- Dynamics/GlobalPersistenceFrontier.lean:2

The third was supplied by the global-persistence branch.  The first two are the Floquet
chain's analytic foundations; see docs/floquet-obligations.md.

`CRNTFrontier` is a library root rather than a module under `CRNT/`, so it is allowed.

Usage:
    python3 scripts/check_imports.py
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOTS = {"CRNTFrontier"}  # library roots that are not modules under CRNT/

IMPORT = re.compile(r"^\s*import\s+((?:CRNT|CRNTFrontier|Scaffold)[\w.]*)\s*$")


def modules() -> set[str]:
    out = set()
    for top in ("CRNT", "Scaffold"):
        for base, _, files in os.walk(os.path.join(ROOT, top)):
            for f in files:
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(base, f), ROOT)
                    out.add(rel[:-5].replace(os.sep, "."))
    if os.path.exists(os.path.join(ROOT, "CRNT.lean")):
        out.add("CRNT")
    for r in ROOTS:
        if os.path.exists(os.path.join(ROOT, r + ".lean")):
            out.add(r)
    return out


def main() -> int:
    known = modules()
    missing: dict[str, list[str]] = {}
    for base, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", "build"}]
        for f in files:
            if not f.endswith(".lean"):
                continue
            path = os.path.relpath(os.path.join(base, f), ROOT)
            with open(os.path.join(ROOT, path), encoding="utf-8", errors="replace") as fh:
                for lineno, line in enumerate(fh, start=1):
                    m = IMPORT.match(line)
                    if m and m.group(1) not in known:
                        missing.setdefault(m.group(1), []).append(f"{path}:{lineno}")

    if missing:
        print(f"::error::{len(missing)} import(s) of modules that do not exist:", file=sys.stderr)
        for mod in sorted(missing):
            print(f"  {mod}", file=sys.stderr)
            for site in missing[mod]:
                print(f"      imported at {site}", file=sys.stderr)
        return 1

    print(f"ok: every internal import resolves ({len(known)} modules on disk)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

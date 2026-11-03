#!/usr/bin/env python3
"""Static integration audit for the global-persistence expansion.

This is not a Lean elaboration check. It is intentionally dependency-free so it can run in
restricted environments before `lake build` is available.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
NEW = [
    ROOT / "CRNT/Geometry/EndotacticGlobal.lean",
    ROOT / "CRNT/Dynamics/GlobalPersistence.lean",
    ROOT / "CRNT/Dynamics/GlobalPermanence.lean",
    ROOT / "CRNT/Dynamics/GlobalPersistenceCertificates.lean",
    ROOT / "CRNT/Dynamics/SingleLinkageStructure.lean",
    ROOT / "CRNT/Dynamics/SiphonAutocatalysis.lean",
    ROOT / "CRNT/Dynamics/TierPersistence.lean",
    ROOT / "CRNT/Dynamics/TierLyapunov.lean",
    ROOT / "CRNT/Decision/StrictConeRealization.lean",
    ROOT / "CRNT/Dynamics/GlobalPersistenceFrontier.lean",
    ROOT / "CRNT/Dynamics/KnownGlobalPersistenceClasses.lean",
]

def strip_comments(text: str) -> str:
    # Adequate for auditing explicit proof-hole commands in these source files.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())

errors: list[str] = []
for path in NEW:
    if not path.exists():
        errors.append(f"missing new module: {path.relative_to(ROOT)}")
        continue
    clean = strip_comments(path.read_text())
    for token in ("sorry", "admit", "axiom"):
        if re.search(rf"\b{token}\b", clean):
            errors.append(f"{path.relative_to(ROOT)} contains proof-hole command {token!r}")

files = list((ROOT / "CRNT").rglob("*.lean"))
graph = {p: [] for p in files}
for path in files:
    for lineno, line in enumerate(path.read_text().splitlines(), 1):
        m = re.match(r"\s*import\s+(CRNT(?:\.[A-Za-z0-9_]+)+)\s*$", line)
        if not m:
            continue
        dep = ROOT.joinpath(*m.group(1).split(".")).with_suffix(".lean")
        if not dep.exists():
            errors.append(
                f"unresolved import {m.group(1)} at {path.relative_to(ROOT)}:{lineno}"
            )
        elif dep in graph:
            graph[path].append(dep)

seen: set[Path] = set()
active: list[Path] = []
active_set: set[Path] = set()

def dfs(path: Path) -> None:
    seen.add(path)
    active.append(path)
    active_set.add(path)
    for dep in graph[path]:
        if dep not in seen:
            dfs(dep)
        elif dep in active_set:
            cycle = active[active.index(dep):] + [dep]
            errors.append("import cycle: " + " -> ".join(str(x.relative_to(ROOT)) for x in cycle))
    active.pop()
    active_set.remove(path)

for path in files:
    if path not in seen:
        dfs(path)

core = (ROOT / "CRNT.lean").read_text()
if "import CRNT.Dynamics.GlobalPersistenceFrontier" in core:
    errors.append("CRNT.lean must not re-export GlobalPersistenceFrontier")

if errors:
    print("global-persistence static audit: FAILED")
    for e in errors:
        print(" -", e)
    sys.exit(1)

print("global-persistence static audit: OK")
print(f" audited {len(NEW)} new modules and {len(files)} CRNT source files")

#!/usr/bin/env python3
"""Static checks for the oscillation expansion when Lean is unavailable.

This is intentionally *not* a replacement for `lake build`.  It catches repository-level mistakes
that are easy to make while developing offline: unresolved internal imports, orphaned oscillation
modules, placeholder proof declarations, and analyzer/docs contract-version drift.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
OSC = ROOT / "CRNT" / "Oscillation"
UMBRELLA = ROOT / "CRNT" / "Oscillation.lean"
ANALYSIS = ROOT / "CRNT" / "Interop" / "Analysis.lean"
DOCS = [ROOT / "docs" / "oscillation.md", ROOT / "docs" / "analyze-contract.md"]

errors: list[str] = []

# 1. Every internal CRNT import resolves to a source file.
for lean in (ROOT / "CRNT").rglob("*.lean"):
    for lineno, line in enumerate(lean.read_text().splitlines(), 1):
        m = re.match(r"\s*import\s+(CRNT(?:\.[A-Za-z0-9_]+)+)\s*$", line)
        if not m:
            continue
        target = ROOT / (m.group(1).replace(".", "/") + ".lean")
        if not target.exists():
            errors.append(f"{lean.relative_to(ROOT)}:{lineno}: unresolved import {m.group(1)}")

# 2. Every oscillation module is exported by the umbrella import.
umbrella_text = UMBRELLA.read_text()
for lean in sorted(OSC.glob("*.lean")):
    module = "CRNT.Oscillation." + lean.stem
    if f"import {module}" not in umbrella_text:
        errors.append(f"{lean.relative_to(ROOT)}: not imported by CRNT/Oscillation.lean")

# 3. No proof escape hatches in code lines of the oscillation layer.
# Ignore comments/docstrings by stripping Lean block comments conservatively.
block_comment = re.compile(r"/-.*?-/", re.S)
for lean in [UMBRELLA, *sorted(OSC.glob("*.lean"))]:
    text = block_comment.sub("", lean.read_text())
    for lineno, line in enumerate(text.splitlines(), 1):
        code = line.split("--", 1)[0]
        if re.search(r"\b(sorry|admit|axiom)\b", code):
            errors.append(f"{lean.relative_to(ROOT)}:{lineno}: proof escape hatch: {code.strip()}")

# 4. Analyzer/docs agree on the contract version.
m = re.search(r"def\s+analysisVersion\s*:\s*Nat\s*:=\s*(\d+)", ANALYSIS.read_text())
if not m:
    errors.append("could not parse analysisVersion")
else:
    version = int(m.group(1))
    for doc in DOCS:
        text = doc.read_text()
        if f"version {version}" not in text and f"`{version}`" not in text and f'"version":{version}' not in text:
            errors.append(f"{doc.relative_to(ROOT)}: does not mention analyzer contract v{version}")
        stale = []
        for v in range(1, version):
            if f"currently `{v}`" in text or re.search(rf"\bContract version {v}\b(?!\d)", text):
                stale.append(v)
        if stale:
            errors.append(f"{doc.relative_to(ROOT)}: stale version markers {stale}")

# 5. The public root import exposes the oscillation umbrella.
root_import = (ROOT / "CRNT.lean").read_text()
if "import CRNT.Oscillation" not in root_import:
    errors.append("CRNT.lean does not import CRNT.Oscillation")

if errors:
    print("oscillation static checks: FAILED")
    for e in errors:
        print(" -", e)
    sys.exit(1)

print("oscillation static checks: PASS")
print(f" - modules: {len(list(OSC.glob('*.lean')))}")
print(" - internal CRNT imports resolve")
print(" - all oscillation modules are public through CRNT.Oscillation")
print(" - no code-level sorry/admit/axiom in oscillation layer")
print(" - analyzer/docs contract version consistent")

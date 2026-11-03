#!/usr/bin/env python3
"""Export elaborated field-map types and audit their axioms.

This checks names, inferred hypotheses, and axiom dependencies. It does not
decide whether a definition or theorem corresponds to its advertised mathematics.
Run from a checkout with the pinned Lean/Mathlib dependencies installed.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"^'([^'\n]+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)


def field_map_rows() -> list[dict]:
    rows = []
    for number, line in enumerate((ROOT / "docs/field-map.md").read_text().splitlines(), 1):
        if not re.match(r"^\| [A-Z]\d+ \|", line):
            continue
        status = re.search(r"\|\s*(proved|partial|stated|missing|open)\s*\|", line)
        if status is None:
            raise ValueError(f"Missing status at field-map line {number}")
        cells = line[: status.start()].strip("| ").split(" | ", 3)
        if len(cells) != 4:
            raise ValueError(f"Malformed field-map row at line {number}")
        rows.append({
            "id": cells[0], "title": cells[1], "line": number,
            "advertised_status": status.group(1),
            "declarations": re.findall(r"`([A-Za-z_][A-Za-z0-9_.]*)`", cells[3]),
        })
    if not rows or len({r["id"] for r in rows}) != len(rows):
        raise ValueError("Empty or duplicated field-map rows")
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=pathlib.Path, required=True, help="Lean type/axiom log")
    parser.add_argument("--metadata", type=pathlib.Path, help="Machine-readable coverage summary")
    args = parser.parse_args()
    rows = field_map_rows()
    names = list(dict.fromkeys(name for row in rows for name in row["declarations"]))
    source = "import CRNT\n" + "".join(f"#check {n}\n#print axioms {n}\n" for n in names)
    with tempfile.TemporaryDirectory(prefix="crnt-semantic-audit-") as directory:
        probe = pathlib.Path(directory) / "AdvertisedStatements.lean"
        probe.write_text(source)
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
        )
    args.output.write_text(result.stdout)
    reports = list(AXIOM_REPORT.finditer(result.stdout))
    found = [m.group(1) for m in reports]
    unexpected = {
        m.group(1): sorted(set(a.strip() for a in (m.group(2) or "").split(",") if a.strip())
                          - STANDARD_AXIOMS)
        for m in reports
    }
    unexpected = {name: axioms for name, axioms in unexpected.items() if axioms}
    summary = {
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "field_map_rows": len(rows), "distinct_declarations": len(names),
        "axiom_reports": len(reports), "missing": sorted(set(names) - set(found)),
        "extra": sorted(set(found) - set(names)), "unexpected_axioms": unexpected,
        "lean_exit_code": result.returncode,
    }
    if args.metadata:
        args.metadata.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return int(bool(result.returncode or summary["missing"] or summary["extra"]
                    or len(reports) != len(names) or unexpected))


if __name__ == "__main__":
    raise SystemExit(main())

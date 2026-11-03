#!/usr/bin/env python3
"""measure.py — the single scalar objective for the CRNT-Lean swarm.

Karpathy-style autoresearch: one number, many trials, keep what improves it.

    python3 research/scripts/measure.py [--ref research/swarm] [--root .]

The objective is lexicographic and is reported both as the tuple and as a single
integer score.  Lower `holes` is strictly better; everything else is tie-breaking
progress that keeps a hole-closing PR from being rejected for unrelated reasons.

  holes          declaration-level executable `sorry`s under CRNT/   (target 0)
  core_ok        1 if `CRNT.lean`'s module set is hole-free on disk
  broken_gates   static CI gates that fail (check_imports, check_stubs,
                 check_undefined_names, check_exclusions)           (target 0)
  frontier_mods  CRNT modules that are hole-free
  scaffold_mods  Scaffold modules that are hole-free
  lean_lines     non-comment non-blank Lean lines under CRNT/ + Scaffold/

Exit status is always 0; a non-zero score here is not an error, it is a datum.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

SORRY_RE = re.compile(r"(?<![A-Za-z_.'\"])\bsorry\b(?![A-Za-z_])")
AXIOM_RE = re.compile(r"^\s*(axiom|constant)\s+\w+", re.M)


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *args],
        check=False,
        capture_output=True,
        text=True,
    ).stdout


def strip_comments(text: str) -> str:
    """Blank out Lean line/block comments, preserving line numbering."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif depth == 0 and text[i] == '"':
            # string literal: copy verbatim until unescaped closing quote
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append(text[i:j])
            i = j
        elif depth == 0 and text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def scan(root: Path) -> dict:
    holes: list[tuple[str, int]] = []
    frontier = scaffold = 0
    lines = 0
    axioms: list[tuple[str, int]] = []

    for base, tag in (("CRNT", "frontier"), ("Scaffold", "scaffold")):
        top = root / base
        if not top.is_dir():
            continue
        for path in sorted(top.rglob("*.lean")):
            raw = path.read_text(encoding="utf-8", errors="replace")
            code = strip_comments(raw)
            body = sum(
                1
                for ln in code.splitlines()
                if ln.strip() and not ln.strip().startswith("--")
            )
            lines += body
            n_here = sum(1 for ln in code.splitlines() if SORRY_RE.search(ln))
            if base == "CRNT" and n_here:
                rel = str(path.relative_to(root))
                for idx, ln in enumerate(code.splitlines(), 1):
                    if SORRY_RE.search(ln):
                        holes.append((rel, idx))
            if tag == "frontier" and n_here == 0:
                frontier += 1
            if tag == "scaffold" and n_here == 0:
                scaffold += 1
            for idx, ln in enumerate(code.splitlines(), 1):
                if AXIOM_RE.match(ln):
                    axioms.append((f"{path.relative_to(root)}", idx))

    return {
        "holes": len(holes),
        "hole_sites": holes,
        "frontier_mods": frontier,
        "scaffold_mods": scaffold,
        "lean_lines": lines,
        "declared_axioms": len(axioms),
        "axiom_sites": axioms,
    }


def gates(root: Path) -> dict:
    out = {}
    for name in (
        "check_imports.py",
        "check_stubs.py",
        "check_undefined_names.py",
        "check_exclusions.py",
    ):
        script = root / "scripts" / name
        if not script.is_file():
            out[name] = "absent"
            continue
        p = subprocess.run(
            [sys.executable, str(script)],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
        out[name] = "pass" if p.returncode == 0 else "FAIL"
    return out


def score(m: dict, g: dict) -> int:
    broken = sum(1 for v in g.values() if v == "FAIL")
    return (
        -1000 * m["holes"]
        - 50 * broken
        - 20 * m["declared_axioms"]
        + min(m["frontier_mods"], 400)
        + min(m["scaffold_mods"], 100)
        + m["lean_lines"] // 500
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--ref", default=None, help="also report this git ref's hole count")
    ap.add_argument("--no-gates", action="store_true")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    m = scan(root)
    g = {} if args.no_gates else gates(root)

    payload = {"metrics": m, "gates": g, "score": score(m, g)}
    if args.ref:
        listing = _git(root, "grep", "-n", "-E", r"\bsorry\b", args.ref, "--", "CRNT").splitlines()
        payload["ref_sorry_lines"] = len(listing)

    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
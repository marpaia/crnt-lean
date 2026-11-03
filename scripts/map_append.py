#!/usr/bin/env python3
"""Append declarations and a note to a leaf row of `docs/field-map.md`.

Usage:  python3 scripts/map_append.py <leaf> <decl> [<decl> ...] -- <note>

The leaf rows are Markdown tables whose *Notes* cells may contain `|` characters (e.g. inside
code spans), so the row is anchored on the status keyword rather than split naively:

* the new declarations are inserted immediately before the status keyword (the Lean column
  ends there);
* the new note is appended at the very end of the row.

The operation is idempotent: a declaration already present in the row is not added again, and
a note already present in the row is not appended again.
"""
from __future__ import annotations

import re
import sys

MAP = "docs/field-map.md"
STATUSES = ("proved", "partial", "missing", "stated", "open")


def main(argv: list[str]) -> int:
    if "--" not in argv:
        print(__doc__)
        return 2
    cut = argv.index("--")
    leaf = argv[0]
    decls = argv[1:cut]
    note = " ".join(argv[cut + 1 :]).strip()

    lines = open(MAP, encoding="utf-8").read().split("\n")
    for i, line in enumerate(lines):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if not cells or cells[0] != leaf:
            continue
        m = None
        for st in STATUSES:
            m = re.search(re.escape(st) + r"\s*\|", line)
            if m:
                break
        if m is None:
            print(f"{leaf}: no status cell found", file=sys.stderr)
            return 1
        # the Lean cell ends just before the status cell, i.e. one `|` before the
        # status keyword: insert the new declarations there, not after that `|`
        cut = line.rfind("|", 0, m.start())
        if cut < 0:
            print(f"{leaf}: no Lean column found", file=sys.stderr)
            return 1
        head = line[:cut]
        tail = line[cut:]
        added = [d for d in decls if f"`{d}`" not in head]
        if added:
            head = head.rstrip() + ", " + ", ".join(f"`{d}`" for d in added) + " "
        if note and note not in line:
            tail = tail.rstrip()
            if tail.endswith("|"):
                tail = tail[:-1].rstrip()
            tail = tail + " " + note + " |"
        lines[i] = head + tail
        print(f"{leaf}: +{len(added)} declaration(s)" + ("" if note and note in line else ", note appended"))
        open(MAP, "w", encoding="utf-8").write("\n".join(lines))
        return 0
    print(f"{leaf}: row not found", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

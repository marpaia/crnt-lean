#!/usr/bin/env python3
"""Extract every `sorry` in the tree together with the declaration that contains it.

The existing triage classifies by keyword match on the enclosing declaration and its
preceding comment, which is a heuristic: a one-step corollary of an already-proved lemma
can be labelled `major-theorem` purely because the word "deficiency" appears near it.
This dumps the actual statements so they can be judged individually.
"""
from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|instance|example|abbrev|structure)\s+([^\s:({\[]+)")
MAJOR = re.compile(
    r"deficiency|shinar|feinberg|matrix.?tree|matrix.tree|toric|concordan|"
    r"birch|horn|jackson|poincar|bendixson|floquet|hopf|ack|product.form",
    re.I)


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
            if d == 0:
                out.append(text[i])
            else:
                # blank the character but keep newlines, or line numbering shifts
                out.append("\n" if text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def main() -> int:
    only_major = "--major" in sys.argv
    records = []
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dp, f)
            mod = os.path.relpath(path, ROOT)[:-5].replace(os.sep, ".")
            raw = open(path, encoding="utf-8", errors="replace").read()
            code = strip_comments(raw)
            lines = raw.split("\n")
            clines = code.split("\n")

            # index every declaration start
            decls = []
            for i, cl in enumerate(clines):
                m = DECL.match(cl)
                if m:
                    decls.append((i, m.group(1), m.group(2)))

            for i, cl in enumerate(clines):
                if not re.search(r"\bsorry\b", cl):
                    continue
                owner = None
                for (di, kind, name) in decls:
                    if di <= i:
                        owner = (di, kind, name)
                    else:
                        break
                if owner is None:
                    continue
                di, kind, name = owner
                stmt = "\n".join(lines[di:min(di + 12, len(lines))])
                # cut the statement at the proof marker
                cut = stmt.find(":= by")
                if cut < 0:
                    cut = stmt.find(" := ")
                if cut >= 0:
                    stmt = stmt[:cut]
                records.append({
                    "mod": mod, "line": i + 1, "kind": kind, "name": name,
                    "stmt": stmt.strip(),
                    "major": bool(MAJOR.search(name) or MAJOR.search(stmt)),
                })

    majors = [r for r in records if r["major"]]
    print(f"total sorries: {len(records)}")
    print(f"keyword-'major': {len(majors)}")
    print(f"distinct declarations with a sorry: "
          f"{len({(r['mod'], r['name']) for r in records})}")
    print()
    seen = set()
    for r in (majors if only_major else records):
        key = (r["mod"], r["name"])
        if key in seen:
            continue
        seen.add(key)
        print("=" * 100)
        print(f"{r['mod']}:{r['line']}  [{r['kind']} {r['name']}]")
        print(r["stmt"])
    return 0


if __name__ == "__main__":
    sys.exit(main())

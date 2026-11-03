#!/usr/bin/env python3
"""Reject a candidate module that uses a forbidden construct.

Forbidden: `sorry`, `admit`, new `axiom` declarations, `native_decide`, `unsafe`,
`@[implemented_by]`, and `partial def`/`partial theorem`.

The check strips comments and string literals first, so prose in a docstring that
mentions "admit" or "sorry" does not trigger it.

    python3 tasks/campaign/check_module.py CRNT/Dynamics/Gronwall.lean ...
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PATTERNS = [
    (r"(?<![A-Za-z_'])sorry(?![A-Za-z_'])", "sorry"),
    (r"(?<![A-Za-z_'])admit(?![A-Za-z_'])", "admit"),
    (r"(?<![A-Za-z_'])native_decide(?![A-Za-z_'])", "native_decide"),
    (r"(?<![A-Za-z_'])unsafe(?![A-Za-z_'])", "unsafe"),
    (r"@\[implemented_by[^\]]*\]", "@[implemented_by]"),
    (r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*axiom\s",
     "axiom declaration"),
    (r"^\s*(?:@\[[^\]]*\]\s*)?partial\s+(?:def|theorem|lemma)\b", "partial declaration"),
]


def strip_comments_and_strings(text: str) -> list[tuple[int, str]]:
    """(line number, code-only line) pairs."""
    out: list[tuple[int, str]] = []
    i, n = 0, len(text)
    depth = 0          # comment nesting
    in_str = False
    in_chr = False
    line = 1
    buf: list[str] = []
    while i < n:
        ch = text[i]
        if ch == "\n":
            out.append((line, "".join(buf)))
            buf = []
            line += 1
            i += 1
            continue
        if depth == 0 and not in_str and not in_chr:
            if text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            if text.startswith("/-", i):
                depth = 1
                i += 2
                continue
            if ch == '"':
                in_str = True
                i += 1
                continue
            if ch == "'":
                in_chr = True
                i += 1
                continue
        elif depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append((line, "".join(buf)))
                buf = []
                line += 1
            i += 1
            continue
        elif in_str or in_chr:
            if ch == "\\":
                i += 2
                continue
            if (in_str and ch == '"') or (in_chr and ch == "'"):
                in_str = in_chr = False
            i += 1
            continue
        buf.append(ch)
        i += 1
    out.append((line, "".join(buf)))
    return out


def main() -> int:
    bad = 0
    for path in sys.argv[1:]:
        p = Path(path)
        if not p.exists():
            print(f"missing: {path}", file=sys.stderr)
            bad += 1
            continue
        for lineno, code in strip_comments_and_strings(p.read_text(encoding="utf-8")):
            for pat, label in PATTERNS:
                if re.search(pat, code):
                    print(f"{path}:{lineno}: forbidden {label}: {code.strip()[:120]}",
                          file=sys.stderr)
                    bad += 1
    if bad:
        print(f"FAIL: {bad} forbidden construct(s)", file=sys.stderr)
        return 1
    print("ok: no forbidden construct in", len(sys.argv) - 1, "module(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

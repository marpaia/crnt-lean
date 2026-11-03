#!/usr/bin/env python3
"""Apply the recurring mechanical fixes catalogued in STATUS.md across the whole tree.

Every rule here was derived from a defect fixed by hand at least twice, and each is a *syntactic*
rewrite that cannot change the meaning of a statement -- renames of Mathlib lemmas that moved,
stale module paths, and dot-notation that resolves to the wrong namespace because a `def` unfolds
to a function type.

Rules are deliberately conservative: nothing here touches proof structure, so a rule can only
turn a failing elaboration into a passing one or leave it failing. Run with `--check` first to see
what would change.

Usage:
    python3 scripts/bulk_fix.py --check
    python3 scripts/bulk_fix.py --apply
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# --- stale Mathlib module paths (four found in the 2026-09-18 drops) -----------------
MODULE_MOVES = {
    'Mathlib.Dynamics.Contracting': 'Mathlib.Topology.MetricSpace.Contracting',
    'Mathlib.LinearAlgebra.SpectralRadius': 'Mathlib.Analysis.Normed.Algebra.Spectrum',
    'Mathlib.Topology.Instances.Pi': 'Mathlib.Topology.Constructions',
    'Mathlib.Topology.MetricSpace.IsCompact': 'Mathlib.Topology.MetricSpace.Bounded',
}

# --- Mathlib lemmas that were renamed or never existed under the name used -----------
LEMMA_RENAMES = [
    (r'\babs_add\b(?!_le)', 'abs_add_le'),
    (r'(?<!Finset\.)\babs_sum_le_sum_abs\b', 'Finset.abs_sum_le_sum_abs'),
    (r'\bFinset\.filter_add_filter_neg_eq\b', 'Finset.sum_filter_add_sum_filter_not'),
    (r'\bSet\.Iio_mem_nhds\b', 'Iio_mem_nhds'),
    (r'\bSet\.Ioi_mem_nhds\b', 'Ioi_mem_nhds'),
]

# --- `Concentration S` unfolds to `S → ℝ`, so `.Positive`/`.Nonnegative` on a term of
# --- that type resolves to `Function.Positive`, which does not exist. -----------------
CONC_FIELDS = ('Positive', 'Nonnegative')


def fix_dot_notation(src: str) -> tuple[str, int]:
    """Rewrite `(expr).Positive` into `Concentration.Positive (expr)`.

    Only fires when the receiver is parenthesised and contains an application, which is the
    shape that arises for `Concentration`-valued expressions; a bare identifier is left alone
    because it may legitimately be a structure.
    """
    n = 0
    for field in CONC_FIELDS:
        pat = re.compile(r'\((?P<e>[^()]*\([^()]*\)[^()]*|[^()]* [^()]*)\)\.' + field + r'\b')

        def sub(m: re.Match) -> str:
            nonlocal n
            n += 1
            return f'Concentration.{field} ({m.group("e")})'

        src = pat.sub(sub, src)
    return src, n


def process(path: str) -> tuple[str, dict[str, int]]:
    src = open(path, encoding='utf-8', errors='replace').read()
    counts: dict[str, int] = {}

    for old, new in MODULE_MOVES.items():
        pat = re.compile(r'^import ' + re.escape(old) + r'$', re.M)
        src, k = pat.subn('import ' + new, src)
        if k:
            counts['module:' + old] = k

    for pat, new in LEMMA_RENAMES:
        src, k = re.subn(pat, new, src)
        if k:
            counts['lemma:' + new] = k

    # The dot-notation rule is only safe on files that actually fail this way: `x.Positive`
    # resolves correctly when `x` is a *variable* of type `Concentration S`, and only breaks
    # when the receiver is an application whose type Lean reports as `S → ℝ`. Applying it
    # blindly would churn 76 sites across 31 already-compiling files.
    if os.environ.get('BULK_FIX_DOT') == '1':
        src, k = fix_dot_notation(src)
        if k:
            counts['dot:Concentration'] = k

    return src, counts


def main() -> int:
    if '--apply' not in sys.argv and '--check' not in sys.argv:
        print(__doc__)
        return 1
    apply = '--apply' in sys.argv
    total: dict[str, int] = {}
    touched = 0
    for r, _d, fs in os.walk(os.path.join(ROOT, 'CRNT')):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(r, f)
            new, counts = process(p)
            if not counts:
                continue
            touched += 1
            rel = os.path.relpath(p, ROOT)
            print(f'{rel}: ' + ', '.join(f'{k}×{v}' for k, v in counts.items()))
            for k, v in counts.items():
                total[k] = total.get(k, 0) + v
            if apply:
                open(p, 'w', encoding='utf-8').write(new)
    print(f'\n{touched} file(s); totals:')
    for k, v in sorted(total.items(), key=lambda kv: -kv[1]):
        print(f'  {v:4d}  {k}')
    if not apply:
        print('\n(dry run; pass --apply to write)')
    return 0


if __name__ == '__main__':
    sys.exit(main())

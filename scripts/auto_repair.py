#!/usr/bin/env python3
"""Automated repair pass: every mechanically-detectable defect class found in this tree.

Each rule below was derived from a defect diagnosed by hand and then seen again. All of them are
syntactic and meaning-preserving in the sense that matters: a rule can turn a declaration that
does not elaborate into one that does, but cannot change what a statement says. Rules that *would*
change a statement (for example weakening a `Prop` to a `Type`) are included only where the
declaration is already rejected by Lean, so there is no working behaviour to break.

    python3 scripts/auto_repair.py --check     # report only
    python3 scripts/auto_repair.py --apply     # rewrite in place

Rules
-----
1. `Prop`-valued structures with data fields. A `Prop` structure may only have proof fields; a
   field of type `ℝ`, `Set _`, `Fin n`, a function, etc. makes Lean refuse to generate the
   projections, and every downstream `C.field` then reports the projection as missing -- which
   reads exactly like an invented name. Six independent instances in this tree.
2. Lean keywords used as declaration names (`partial`, `end`, `where`, ...). Produces a *parse*
   error, so the whole module is lost; one instance blocked 38 sorry-free modules.
3. `rw [...] at X.field` / `norm_num at X.field`. The `at` target must be a local hypothesis, not
   a projection.
4. `noncomputable theorem`. Redundant -- theorems generate no code -- and an error, not a warning.
5. Stale Mathlib module paths and renamed lemmas (tables below).
"""

from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MODULE_MOVES = {
    'Mathlib.Dynamics.Contracting': 'Mathlib.Topology.MetricSpace.Contracting',
    'Mathlib.LinearAlgebra.SpectralRadius': 'Mathlib.Analysis.Normed.Algebra.Spectrum',
    'Mathlib.Topology.Instances.Pi': 'Mathlib.Topology.Constructions',
    'Mathlib.Topology.MetricSpace.IsCompact': 'Mathlib.Topology.MetricSpace.Bounded',
}

LEMMA_RENAMES = [
    (r'(?<![\w.])Function\.update_noteq(?![\w])', 'Function.update_of_ne'),
    (r'(?<![\w.])LinearMap\.finrank_map_le(?![\w])', 'Submodule.finrank_map_le'),
    (r'(?<![\w.])Submodule\.finrank_top(?![\w])', 'finrank_top'),
    (r'(?<![\w.])LinearEquiv\.quotKerEquivRange(?![\w])', 'LinearMap.quotKerEquivRange'),
    (r'(?<![\w.])Set\.Iio_mem_nhds(?![\w])', 'Iio_mem_nhds'),
    (r'(?<![\w.])Set\.Ioi_mem_nhds(?![\w])', 'Ioi_mem_nhds'),
    (r'(?<![\w.])abs_add(?![\w_])', 'abs_add_le'),
    (r'(?<!Finset\.)(?<![\w.])abs_sum_le_sum_abs(?![\w])', 'Finset.abs_sum_le_sum_abs'),
    (r'(?<![\w.])Finset\.filter_add_filter_neg_eq(?![\w])',
     'Finset.sum_filter_add_sum_filter_not'),
]

KEYWORDS = ('partial', 'unsafe', 'mutual', 'deriving', 'macro', 'notation', 'instance')

# field types that make a structure carry data rather than proofs
DATA_FIELD = re.compile(
    r'^\s*\w+\s*:\s*('
    r'ℝ|ℕ|ℤ|ℚ|Fin\b|Set\b|Finset\b|Matrix\b|Complex\b|Concentration\b|Submodule\b'
    r'|.*\s→\s.*'
    r')\s*$')
# ... but a field stating a proposition is fine even if those words appear
PROOF_ISH = re.compile(r'[=≤<>∈∀∃∧∨¬↔]|Prop\b|True\b|False\b')


def fix_prop_structures(src: str) -> tuple[str, int]:
    lines = src.split('\n')
    out = list(lines)
    n = 0
    i = 0
    while i < len(lines):
        if not lines[i].startswith('structure '):
            i += 1
            continue
        # the declaration head may span several lines, ending in `where`
        j = i
        head = []
        while j < len(lines) and 'where' not in lines[j]:
            head.append(lines[j])
            j += 1
            if j - i > 8:
                break
        if j >= len(lines):
            i += 1
            continue
        head.append(lines[j])
        head_txt = '\n'.join(head)
        if not re.search(r':\s*Prop\s+where', head_txt):
            i = j + 1
            continue
        # collect the field block
        k = j + 1
        data = []
        while k < len(lines) and (lines[k].startswith('  ') or not lines[k].strip()):
            if DATA_FIELD.match(lines[k]) and not PROOF_ISH.search(lines[k].split(':', 1)[-1]):
                data.append(lines[k].strip())
            k += 1
        if data:
            # drop the `: Prop` ascription on whichever head line carries it
            for idx in range(i, j + 1):
                if re.search(r':\s*Prop\s+where', out[idx]):
                    out[idx] = re.sub(r'\s*:\s*Prop(\s+where)', r'\1', out[idx])
                    n += 1
                    break
                if re.search(r':\s*Prop\s*$', out[idx]):
                    out[idx] = re.sub(r'\s*:\s*Prop\s*$', '', out[idx])
                    n += 1
                    break
        i = k
    return '\n'.join(out), n


def fix_keyword_names(src: str) -> tuple[str, int]:
    n = 0
    for kw in KEYWORDS:
        if not re.search(r'^(?:noncomputable )?(?:def|abbrev|theorem)\s+' + kw + r'\b', src, re.M):
            continue
        src, k = re.subn(r'(?<![\w.])' + kw + r'(?![\w])', kw + 'Deriv' if kw == 'partial'
                         else kw + "'", src)
        n += k
    return src, n


def fix_rw_at_projection(src: str) -> tuple[str, int]:
    pat = re.compile(
        r'^(?P<i>\s*)rw \[(?P<r>[^\]]*)\] at (?P<o>[A-Za-z_]\w*)\.(?P<f>\w+)\n'
        r'(?P=i)(?P<t>norm_num|simp|linarith) at (?P=o)\.(?P=f)\n', re.M)

    def sub(m: re.Match) -> str:
        i, r, o, f, t = m.group('i'), m.group('r'), m.group('o'), m.group('f'), m.group('t')
        return (f'{i}have hproj := {o}.{f}\n{i}rw [{r}] at hproj\n{i}{t} at hproj\n')

    return pat.subn(sub, src)


def process(path: str) -> tuple[str, dict[str, int]]:
    src = open(path, encoding='utf-8', errors='replace').read()
    counts: dict[str, int] = {}

    for old, new in MODULE_MOVES.items():
        src, k = re.subn(r'^import ' + re.escape(old) + r'$', 'import ' + new, src, flags=re.M)
        if k:
            counts['module-move'] = counts.get('module-move', 0) + k
    for pat, new in LEMMA_RENAMES:
        src, k = re.subn(pat, new, src)
        if k:
            counts['lemma-rename'] = counts.get('lemma-rename', 0) + k
    src, k = re.subn(r'^noncomputable theorem ', 'theorem ', src, flags=re.M)
    if k:
        counts['noncomputable-theorem'] = k
    src, k = fix_prop_structures(src)
    if k:
        counts['prop-with-data'] = k
    src, k = fix_keyword_names(src)
    if k:
        counts['keyword-name'] = k
    src, k = fix_rw_at_projection(src)
    if k:
        counts['rw-at-projection'] = k
    return src, counts


def main() -> int:
    if not ({'--check', '--apply'} & set(sys.argv)):
        print(__doc__)
        return 1
    apply = '--apply' in sys.argv
    total: dict[str, int] = {}
    files = 0
    for r, _d, fs in os.walk(os.path.join(ROOT, 'CRNT')):
        for f in sorted(fs):
            if not f.endswith('.lean'):
                continue
            p = os.path.join(r, f)
            new, counts = process(p)
            if not counts:
                continue
            files += 1
            print(os.path.relpath(p, ROOT) + ': ' +
                  ', '.join(f'{k}×{v}' for k, v in counts.items()))
            for k, v in counts.items():
                total[k] = total.get(k, 0) + v
            if apply:
                open(p, 'w', encoding='utf-8').write(new)
    print(f'\n{files} file(s) affected')
    for k, v in sorted(total.items(), key=lambda kv: -kv[1]):
        print(f'  {v:4d}  {k}')
    if not apply:
        print('\n(dry run; pass --apply)')
    return 0


if __name__ == '__main__':
    sys.exit(main())

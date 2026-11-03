#!/usr/bin/env python3
"""crnt_lint: an error-driven checker and fixer for everything that is not mathematics.

Earlier scripts in this directory are *pattern*-driven: they scan source text for shapes known to
be wrong. That approach is exhausted -- `auto_repair.py` now reports zero on every rule. This one
is *error*-driven instead: it elaborates a module, reads Lean's own diagnostics, maps each
diagnostic class to a repair, applies the repairs, and re-elaborates, looping to a fixpoint.

The distinction matters because the remaining defects are not visible in the source. A missing
`noncomputable`, a projection that was never generated, a name that exists two modules away -- none
of these look wrong on the page. Only the compiler knows.

What it will NOT touch
----------------------
`unsolved goals`, `linarith failed`, `ring failed`, and `declaration uses 'sorry'` are reported and
left alone. Those are proof obligations: they need a mathematician, not a mechanic. The whole point
of this tool is to clear everything else so that what remains is honestly mathematical.

Repairs, each keyed to the exact diagnostic that triggers it
-----------------------------------------------------------
    consider marking it as 'noncomputable'        -> insert the modifier
    'theorem' subsumes 'noncomputable'            -> strip the modifier
    failed to generate projection ... 'Prop'       -> drop the `: Prop` ascription
    unexpected token 'kw'; expected identifier     -> rename the keyword-named declaration
    Unexpected term X.f; expected single reference -> bind the projection to a hypothesis first
    Unknown constant / identifier / Invalid field  -> add the import that declares it, or rename
                                                      via the near-miss table, or report as absent
    simp made no progress / No goals to be solved  -> delete the now-redundant closing tactic
    This simp argument is unused                   -> drop that argument
    Try `simp at h` instead of `simpa using h`     -> apply the suggestion

Usage
-----
    python3 scripts/crnt_lint.py --check MODULE...      # diagnose, classify, change nothing
    python3 scripts/crnt_lint.py --fix MODULE...        # repair to a fixpoint
    python3 scripts/crnt_lint.py --fix --ledger         # every ledgered module
    python3 scripts/crnt_lint.py --fix --ledger --sorry-free   # ...that has no `sorry`
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_ROUNDS = 6

# Diagnostics that are mathematics, not mechanics. Never touched.
MATH = (
    'unsolved goals', 'linarith failed', 'nlinarith failed', 'omega could not',
    "ring_nf made no progress on the goal", 'failed to prove positivity',
    "declaration uses 'sorry'", 'could not prove', 'fail to show termination',
)

NEAR_MISS = {
    'Function.update_noteq': 'Function.update_of_ne',
    'LinearMap.finrank_map_le': 'Submodule.finrank_map_le',
    'Submodule.finrank_top': 'finrank_top',
    'LinearEquiv.quotKerEquivRange': 'LinearMap.quotKerEquivRange',
    'Set.Iio_mem_nhds': 'Iio_mem_nhds',
    'Set.Ioi_mem_nhds': 'Ioi_mem_nhds',
    'abs_add': 'abs_add_le',
    'abs_sum_le_sum_abs': 'Finset.abs_sum_le_sum_abs',
    'Finset.filter_add_filter_neg_eq': 'Finset.sum_filter_add_sum_filter_not',
    'Submodule.finrank_eq_zero': 'Submodule.finrank_eq_zero',
}

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*'
    r'(?:theorem|lemma|def|structure|abbrev|inductive|instance|class)\s+([A-Za-z_][\w.\']*)')


# ---------------------------------------------------------------- infrastructure

def mod_to_path(m: str) -> str:
    return m.replace('.', '/') + '.lean' if not m.endswith('.lean') else m


def elaborate(path: str) -> str:
    p = subprocess.run(['lean', path], capture_output=True, text=True, cwd=ROOT)
    return p.stdout + p.stderr


def diagnostics(out: str, path: str) -> list[tuple[int, int, str]]:
    """(line, col, message) for this file only."""
    res = []
    for m in re.finditer(re.escape(path) + r':(\d+):(\d+): (?:error|warning)[^:]*: (.*)', out):
        res.append((int(m.group(1)), int(m.group(2)), m.group(3)))
    return res


def build_decl_index() -> dict[str, list[str]]:
    idx: dict[str, list[str]] = {}
    for r, _d, fs in os.walk(os.path.join(ROOT, 'CRNT')):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            rel = os.path.relpath(os.path.join(r, f), ROOT)
            mod = rel[:-5].replace(os.sep, '.')
            ns: list[str] = []
            for line in open(os.path.join(r, f), encoding='utf-8', errors='replace'):
                nm = re.match(r'^namespace\s+([\w.]+)', line)
                if nm:
                    ns.append(nm.group(1))
                    continue
                if re.match(r'^end\s+[\w.]+', line) and ns:
                    ns.pop()
                    continue
                d = DECL.match(line)
                if d:
                    for name in {d.group(1), '.'.join(ns + [d.group(1)])}:
                        idx.setdefault(name, [])
                        if mod not in idx[name]:
                            idx[name].append(mod)
    return idx


# ---------------------------------------------------------------- repairs

def add_import(lines: list[str], mod: str) -> bool:
    if any(l.strip() == f'import {mod}' for l in lines):
        return False
    last = max((i for i, l in enumerate(lines) if l.startswith('import ')), default=-1)
    lines.insert(last + 1, f'import {mod}')
    return True


def decl_line_above(lines: list[str], ln: int) -> int | None:
    for i in range(min(ln, len(lines)) - 1, -1, -1):
        if DECL.match(lines[i]):
            return i
    return None


def repair(path: str, diags: list[tuple[int, int, str]], idx: dict[str, list[str]],
           report: dict[str, int]) -> tuple[bool, list[str]]:
    """Apply every repair we can justify from these diagnostics. Returns (changed, notes)."""
    full = os.path.join(ROOT, path)
    lines = open(full, encoding='utf-8', errors='replace').read().split('\n')
    changed = False
    notes: list[str] = []
    self_mod = path[:-5].replace(os.sep, '.')
    # Work from the bottom so line numbers stay valid as we edit.
    for ln, _col, msg in sorted(diags, key=lambda d: -d[0]):
        i = ln - 1
        if i < 0 or i >= len(lines):
            continue
        if 'object file' in msg and 'does not exist' in msg:
            # a dependency has not been built yet; not a defect in this module
            report['cascade'] = report.get('cascade', 0) + 1
            continue

        if "invalid 'import' command" in msg:
            # imports must precede all other content; move any stragglers to the import block
            body = [l for l in lines if not re.match(r'^import\s', l)]
            imps, seen = [], set()
            for l in lines:
                if re.match(r'^import\s', l) and l not in seen:
                    seen.add(l); imps.append(l)
            lines = imps + body
            changed = True
            report['import-misplaced'] = report.get('import-misplaced', 0) + 1
            continue

        if any(k in msg for k in MATH):
            report['left-for-mathematician'] = report.get('left-for-mathematician', 0) + 1
            continue

        if "consider marking it as 'noncomputable'" in msg:
            j = decl_line_above(lines, ln)
            if j is not None and not lines[j].startswith('noncomputable'):
                lines[j] = 'noncomputable ' + lines[j]
                changed = True
                report['noncomputable-added'] = report.get('noncomputable-added', 0) + 1
            continue

        if "subsumes 'noncomputable'" in msg:
            j = decl_line_above(lines, ln)
            if j is not None:
                lines[j] = lines[j].replace('noncomputable ', '', 1)
                changed = True
                report['noncomputable-removed'] = report.get('noncomputable-removed', 0) + 1
            continue

        if 'failed to generate projection' in msg and 'Prop' in msg:
            for j in range(max(0, i - 8), min(len(lines), i + 2)):
                if re.search(r':\s*Prop\s+where', lines[j]):
                    lines[j] = re.sub(r'\s*:\s*Prop(\s+where)', r'\1', lines[j])
                    changed = True
                    report['prop-with-data'] = report.get('prop-with-data', 0) + 1
                    break
            continue

        km = re.search(r"unexpected token '(\w+)'; expected identifier", msg)
        if km:
            kw = km.group(1)
            src = '\n'.join(lines)
            src = re.sub(r'(?<![\w.])' + kw + r'(?![\w])', kw + 'Decl', src)
            lines = src.split('\n')
            changed = True
            report['keyword-name'] = report.get('keyword-name', 0) + 1
            continue

        pm = re.search(r'Unexpected term `([A-Za-z_]\w*)\.(\w+)`', msg)
        if pm:
            obj, fld = pm.group(1), pm.group(2)
            ind = re.match(r'\s*', lines[i]).group(0)
            lines[i] = lines[i].replace(f'{obj}.{fld}', 'hproj')
            if i + 1 < len(lines) and f'{obj}.{fld}' in lines[i + 1]:
                lines[i + 1] = lines[i + 1].replace(f'{obj}.{fld}', 'hproj')
            lines.insert(i, f'{ind}have hproj := {obj}.{fld}')
            changed = True
            report['rw-at-projection'] = report.get('rw-at-projection', 0) + 1
            continue

        nm = re.search(r'(?:Unknown constant|Unknown identifier|does not contain|Invalid field) '
                       r'`?([A-Za-z_][\w.\']*)`?', msg)
        if nm:
            name = nm.group(1).rstrip('`')
            if name in NEAR_MISS and NEAR_MISS[name] != name:
                src = '\n'.join(lines).replace(name, NEAR_MISS[name])
                lines = src.split('\n')
                changed = True
                report['near-miss-rename'] = report.get('near-miss-rename', 0) + 1
                continue
            owners = [m for m in idx.get(name, []) if m != self_mod]
            if owners and add_import(lines, owners[0]):
                changed = True
                report['import-added'] = report.get('import-added', 0) + 1
                notes.append(f'  + import {owners[0]}  (for {name})')
            elif not owners:
                if self_mod in idx.get(name, []):
                    report['local-decl-failed'] = report.get('local-decl-failed', 0) + 1
                    notes.append(f'  ! {name} is declared in this file but its declaration failed')
                else:
                    report['name-absent'] = report.get('name-absent', 0) + 1
                    notes.append(f'  ! {name} is not declared anywhere -- needs a rewrite')
            continue

        if 'made no progress' in msg or 'No goals to be solved' in msg:
            # the tactic on this line is now redundant; drop it
            if re.match(r'\s*(simp|ring|norm_num|rfl|omega|dsimp|push_cast|linarith)\b',
                        lines[i]):
                del lines[i]
                changed = True
                report['redundant-tactic-removed'] = \
                    report.get('redundant-tactic-removed', 0) + 1
            continue

        um = re.search(r'This simp argument is unused:\s*(\S+)', msg)
        if um:
            arg = um.group(1)
            for j in range(i, min(len(lines), i + 4)):
                if arg in lines[j]:
                    lines[j] = re.sub(r',\s*' + re.escape(arg) + r'\b', '', lines[j])
                    lines[j] = re.sub(r'\b' + re.escape(arg) + r'\s*,\s*', '', lines[j])
                    changed = True
                    report['unused-simp-arg'] = report.get('unused-simp-arg', 0) + 1
                    break
            continue

        if 'instead of `simpa using' in msg or 'Try `simp at' in msg:
            m2 = re.match(r'(\s*)simpa(.*) using (\w+)\s*$', lines[i])
            if m2:
                lines[i] = f'{m2.group(1)}simp{m2.group(2)} at {m2.group(3)}'
                changed = True
                report['simpa-to-simp-at'] = report.get('simpa-to-simp-at', 0) + 1
            continue

        report['unhandled'] = report.get('unhandled', 0) + 1
        notes.append(f'  ? {path}:{ln} {msg[:70]}')

    if changed:
        open(full, 'w', encoding='utf-8').write('\n'.join(lines))
    return changed, notes


# ---------------------------------------------------------------- driver

def main() -> int:
    argv = sys.argv[1:]
    fix = '--fix' in argv
    if not fix and '--check' not in argv:
        print(__doc__)
        return 1
    mods = [a for a in argv if not a.startswith('--')]
    if '--ledger' in argv:
        led = os.path.join(ROOT, 'scripts', 'unverified_modules.txt')
        mods = [l.strip() for l in open(led) if l.strip() and not l.startswith('#')]
        if '--sorry-free' in argv:
            keep = []
            for m in mods:
                p = os.path.join(ROOT, mod_to_path(m))
                if os.path.exists(p) and not re.search(
                        r'^\s*sorry\b', open(p, encoding='utf-8', errors='replace').read(), re.M):
                    keep.append(m)
            mods = keep

    idx = build_decl_index()
    report: dict[str, int] = {}
    all_notes: list[str] = []
    fixed_clean: list[str] = []

    for m in mods:
        path = mod_to_path(m)
        if not os.path.exists(os.path.join(ROOT, path)):
            continue
        for _round in range(MAX_ROUNDS if fix else 1):
            out = elaborate(path)
            diags = [d for d in diagnostics(out, path) if 'error' in out]
            errs = [d for d in diagnostics(out, path)]
            if not errs:
                break
            if not fix:
                for ln, _c, msg in errs:
                    cat = 'MATH' if any(k in msg for k in MATH) else 'mech'
                    all_notes.append(f'  [{cat}] {path}:{ln} {msg[:70]}')
                    report[cat] = report.get(cat, 0) + 1
                break
            changed, notes = repair(path, errs, idx, report)
            all_notes.extend(notes)
            if not changed:
                break
        else:
            pass
        if fix:
            out = elaborate(path)
            if not re.search(re.escape(path) + r':\d+:\d+: error', out):
                fixed_clean.append(m)

    print(f'{len(mods)} module(s) examined')
    if fixed_clean:
        print(f'\nnow elaborating cleanly ({len(fixed_clean)}):')
        for m in fixed_clean:
            print(f'  {m}')
    print('\ncounts:')
    for k, v in sorted(report.items(), key=lambda kv: -kv[1]):
        print(f'  {v:5d}  {k}')
    uniq = []
    for n in all_notes:
        if n not in uniq:
            uniq.append(n)
    if uniq:
        print('\nnotes:')
        for n in uniq[:60]:
            print(n)
    return 0


if __name__ == '__main__':
    sys.exit(main())

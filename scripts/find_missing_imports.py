#!/usr/bin/env python3
"""Find `unknown constant` / `invalid field` errors caused by a *missing import*.

Three different situations produce an identical "unknown constant" message in this tree, and
they need opposite responses:

  1. the name was invented and does not exist anywhere  -> the module needs rewriting;
  2. the name exists in another module that is not imported -> one-line import fix;
  3. the name is declared locally but its own declaration failed to elaborate -> fix that first.

This script separates them mechanically. It elaborates each module, collects the names Lean
could not resolve, and looks each one up in an index of every declaration in the tree. Case (2)
is reported with the exact `import` line to add; case (1) is reported as genuinely absent.

Usage:
    python3 scripts/find_missing_imports.py [module ...]     # default: every ledgered module
    python3 scripts/find_missing_imports.py --apply          # insert the imports it is sure about
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |private |protected )*'
    r'(?:theorem|lemma|def|structure|abbrev|inductive|instance|class)\s+'
    r'([A-Za-z_][\w.\']*)', re.M)
UNKNOWN = re.compile(r"(?:Unknown constant|Unknown identifier|does not contain)\s+`?([A-Za-z_][\w.\']*)`?")
FIELD = re.compile(r"Invalid field `([A-Za-z_][\w']*)`")


def all_lean_files() -> list[str]:
    out = []
    for r, _d, fs in os.walk(os.path.join(ROOT, 'CRNT')):
        for f in fs:
            if f.endswith('.lean'):
                out.append(os.path.relpath(os.path.join(r, f), ROOT))
    return sorted(out)


def build_index() -> dict[str, list[str]]:
    """Map every declared short name and its namespaced suffixes to the modules declaring it."""
    idx: dict[str, list[str]] = {}
    for f in all_lean_files():
        mod = f[:-5].replace(os.sep, '.')
        src = open(os.path.join(ROOT, f), encoding='utf-8', errors='replace').read()
        # track the enclosing namespace so we can register qualified names too
        ns: list[str] = []
        for line in src.split('\n'):
            m = re.match(r'^namespace\s+([\w.]+)', line)
            if m:
                ns.append(m.group(1))
                continue
            if re.match(r'^end\s+[\w.]+', line) and ns:
                ns.pop()
                continue
            d = DECL.match(line)
            if d:
                short = d.group(1)
                for name in {short, '.'.join(ns + [short])}:
                    idx.setdefault(name, [])
                    if mod not in idx[name]:
                        idx[name].append(mod)
    return idx


def module_imports(path: str) -> set[str]:
    src = open(os.path.join(ROOT, path), encoding='utf-8', errors='replace').read()
    return set(re.findall(r'^import\s+(CRNT[\w.]*)', src, re.M))


def elaborate(path: str) -> str:
    env = dict(os.environ)
    proc = subprocess.run(['lean', path], capture_output=True, text=True, cwd=ROOT, env=env)
    return proc.stdout + proc.stderr


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    apply = '--apply' in sys.argv
    idx = build_index()

    if args:
        paths = [a.replace('.', '/') + '.lean' if not a.endswith('.lean') else a for a in args]
    else:
        led = os.path.join(ROOT, 'scripts', 'unverified_modules.txt')
        mods = [l.strip() for l in open(led) if l.strip() and not l.startswith('#')]
        paths = [m.replace('.', '/') + '.lean' for m in mods]

    fixable: dict[str, set[str]] = {}
    absent: dict[str, set[str]] = {}
    for p in paths:
        if not os.path.exists(os.path.join(ROOT, p)):
            continue
        out = elaborate(p)
        names = set(UNKNOWN.findall(out)) | set(FIELD.findall(out))
        if not names:
            continue
        have = module_imports(p)
        self_mod = p[:-5].replace(os.sep, '.')
        for n in names:
            owners = [m for m in idx.get(n, []) if m != self_mod]
            if not owners:
                # declared locally, or genuinely absent
                if n in idx and self_mod in idx[n]:
                    continue  # case (3): local declaration failed; not an import problem
                absent.setdefault(p, set()).add(n)
            elif not (set(owners) & have):
                fixable.setdefault(p, set()).add(owners[0])

    print(f"=== missing imports ({len(fixable)} module(s)) ===")
    for p, mods in sorted(fixable.items()):
        print(f"{p}")
        for m in sorted(mods):
            print(f"    import {m}")
    print(f"\n=== names not declared anywhere ({len(absent)} module(s)) ===")
    for p, names in sorted(absent.items()):
        print(f"{p}: {', '.join(sorted(names))}")

    if apply:
        for p, mods in fixable.items():
            full = os.path.join(ROOT, p)
            src = open(full, encoding='utf-8').read()
            lines = src.split('\n')
            last = max(i for i, l in enumerate(lines) if l.startswith('import '))
            add = [f'import {m}' for m in sorted(mods) if f'import {m}' not in src]
            lines = lines[:last + 1] + add + lines[last + 1:]
            open(full, 'w', encoding='utf-8').write('\n'.join(lines))
        print(f"\napplied imports to {len(fixable)} module(s)")
    return 0


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Compile CRNT modules with `lean` directly, in dependency order, without Lake.

Lake cannot be used in this environment: on first invocation it decided the mathlib
package URL had changed, deleted `.lake/packages/mathlib`, and tried to clone from
github (blocked). This driver replaces it for the narrow job of elaborating project
modules against a supplied compiled dependency cache.

It computes the transitive closure of a target module's `import CRNT...` lines,
topologically sorts it, and compiles each module to `.lake/build/lib/lean/<Mod>.olean`
with the four companion outputs Lean 4.31 expects. Already-current oleans are skipped,
so reruns are incremental.

Usage:
    python3 scripts/offline_build.py CRNT.Examples.Lotka [more modules...]
    python3 scripts/offline_build.py --plan CRNT.Examples.Lotka   # print order, compile nothing
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
CACHE_GLOB_PARENT = os.environ.get(
    "CRNT_CACHE", "/home/claude/crnt-compiled-cache")

IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)


def module_src(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def module_olean(mod: str) -> str:
    return os.path.join(BUILD, mod.replace(".", os.sep) + ".olean")


def deps(mod: str) -> list[str]:
    src = module_src(mod)
    if not os.path.exists(src):
        return []
    with open(src, encoding="utf-8", errors="replace") as fh:
        return IMPORT.findall(fh.read())


def closure(targets: list[str]) -> list[str]:
    """Transitive closure, topologically sorted (dependencies first)."""
    order: list[str] = []
    state: dict[str, int] = {}  # 0 = visiting, 1 = done

    def visit(mod: str, stack: list[str]) -> None:
        if state.get(mod) == 1:
            return
        if state.get(mod) == 0:
            cyc = " -> ".join(stack[stack.index(mod):] + [mod])
            raise SystemExit(f"import cycle: {cyc}")
        if not os.path.exists(module_src(mod)):
            raise SystemExit(f"no source file for module {mod}")
        state[mod] = 0
        for d in deps(mod):
            visit(d, stack + [mod])
        state[mod] = 1
        order.append(mod)

    for t in targets:
        visit(t, [])
    return order


def lean_path() -> str:
    roots = []
    parent = CACHE_GLOB_PARENT
    if os.path.isdir(parent):
        for name in sorted(os.listdir(parent)):
            d = os.path.join(parent, name, ".lake", "build", "lib", "lean")
            if os.path.isdir(d):
                roots.append(d)
    roots.append(BUILD)  # project's own build output
    return ":".join(roots)


def up_to_date(mod: str) -> bool:
    ol, src = module_olean(mod), module_src(mod)
    if not os.path.exists(ol):
        return False
    if os.path.getmtime(ol) < os.path.getmtime(src):
        return False
    # a stale olean whose dependency was rebuilt later must also be redone
    for d in deps(mod):
        dol = module_olean(d)
        if os.path.exists(dol) and os.path.getmtime(ol) < os.path.getmtime(dol):
            return False
    return True


def compile_module(mod: str, env: dict[str, str]) -> tuple[bool, str, float]:
    src = module_src(mod)
    base = os.path.join(BUILD, mod.replace(".", os.sep))
    os.makedirs(os.path.dirname(base), exist_ok=True)
    cmd = [
        "lean", src,
        "-o", base + ".olean",
        "-i", base + ".ilean",
        "--root", ROOT,
    ]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return proc.returncode == 0, (proc.stdout + proc.stderr).strip(), time.time() - t0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("modules", nargs="+")
    ap.add_argument("--plan", action="store_true", help="print build order only")
    ap.add_argument("--keep-going", action="store_true",
                    help="continue past a failing module")
    args = ap.parse_args()

    order = closure(args.modules)
    print(f"closure: {len(order)} module(s)")
    if args.plan:
        for i, m in enumerate(order, 1):
            mark = "  (cached)" if up_to_date(m) else ""
            print(f"  {i:3d}. {m}{mark}")
        return 0

    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path()

    failures: list[tuple[str, str]] = []
    built = skipped = 0
    for i, mod in enumerate(order, 1):
        if up_to_date(mod):
            skipped += 1
            continue
        ok, out, secs = compile_module(mod, env)
        if ok:
            built += 1
            note = f"  [{out.splitlines()[0][:60]}]" if out else ""
            print(f"[{i}/{len(order)}] ok    {mod}  ({secs:.1f}s){note}")
        else:
            failures.append((mod, out))
            print(f"[{i}/{len(order)}] FAIL  {mod}  ({secs:.1f}s)")
            print("    " + "\n    ".join(out.splitlines()[:12]))
            if not args.keep_going:
                break

    print(f"\nbuilt {built}, cached {skipped}, failed {len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

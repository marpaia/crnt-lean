#!/usr/bin/env python3
"""Classify Lean failures against the known defect catalogue, and batch-apply safe fixes.

Rationale: most of this tree's failures are a handful of recurring, mechanical defects, and
reading files one at a time to rediscover them is the slow way. This elaborates every target,
buckets each diagnostic by pattern, and tells you which buckets are auto-fixable — so a whole
defect *class* gets fixed in one pass instead of one module per round trip.

`--apply` only touches the classes where the fix is determined by the error itself:

  noncomputable     Lean names the exact line and the required keyword.
  notation-scope    `⟪..⟫_ℝ` needs `open scoped InnerProductSpace` (NOT
                    RealInnerProductSpace, which gives the unsuffixed bracket).
  bigop-binder      `∑ x in s` -> `∑ x ∈ s`.
  noncomputable-thm `noncomputable theorem` is always an error: theorems emit no code.
  missing-import    only when the unresolved name is declared in exactly ONE module in the
                    tree and importing it cannot create a cycle.

Everything else is reported with a suggestion and left alone, because the fix needs a human
look at the goal. Each auto-fix is verified by re-elaborating the module; a fix that does not
reduce the error count is reverted.

Usage
    python3 scripts/triage.py --targets scripts/unverified_modules.txt
    python3 scripts/triage.py --targets FILE --apply
    python3 scripts/triage.py --module CRNT.Foo.Bar
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "lean")
CACHE = os.environ.get("CRNT_CACHE", "")
IMPORT = re.compile(r"^import\s+(CRNT[\w.]*)\s*$", re.M)
DECL_ANY = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s:({\[]+)",
    re.M)

# (bucket, regex, human-readable suggestion)
PATTERNS = [
    ("noncomputable", r"dependsOnNoncomputable",
     "add `noncomputable` to the def named at that line"),
    ("notation-scope", r"expected token",
     "if the line uses `⟪..⟫_ℝ`: add `open scoped InnerProductSpace`"),
    ("stale-mathlib-path", r"object file '.*Mathlib.*' of module (\S+) does not exist",
     "Mathlib module moved in 4.31; grep the mathlib source for the notation/decl"),
    ("missing-dep-olean", r"object file '.*/CRNT/.*' of module (\S+) does not exist",
     "dependency not built yet; build its closure first"),
    ("bad-dot-notation", r"Invalid field notation: Function `([^`]+)` does not have a usable",
     "receiver-less function in a namespace; drop the `N.`/`G.` receiver"),
    ("invalid-field", r"invalidField.*Invalid field `([^`]+)`",
     "field/decl does not exist: either a missing import or an invented name"),
    ("unknown-ident", r"unknownIdentifier.*Unknown identifier `([^`]+)`",
     "missing import, or a near-miss lemma name"),
    ("unknown-const", r"[Uu]nknown constant '([^']+)'",
     "missing import, or a near-miss lemma name"),
    ("stuck-instance", r"typeclass instance problem is stuck",
     "often a receiver-prefixed call to a `{N : ...}`-implicit function; drop the receiver"),
    ("unfold-absent", r"Tactic `unfold` failed to unfold `([^`]+)`",
     "`unfold A B at h ⊢` errors if either location lacks a name; use `simp only [A, B]`"),
    ("simp-no-progress", r"`simp` made no progress",
     "the goal is already in normal form; try `exact`/`rfl`, or name the unfolding"),
    ("simpa-mismatch", r"After simplification, term",
     "definitional-vs-syntactic mismatch; replace `simpa` with `exact`"),
    ("rewrite-no-match", r"Did not find an occurrence of the pattern",
     "pattern absent (often a coercion); use the iff's `.mpr` or `linear_combination`"),
    ("unsolved-goals", r"unsolved goals", "genuine proof gap; read the goal"),
    ("type-mismatch", r"[Tt]ype mismatch", "check argument order / implicit coercions"),
    ("apply-failed", r"Tactic `apply` failed", "wrong lemma shape"),
    ("assumption-failed", r"Tactic `assumption` failed",
     "hypothesis not in scope; anonymous arrow binders need naming"),
    ("no-goals", r"No goals to be solved", "cascade from an earlier error; fix that first"),
]
AUTO = {"noncomputable", "notation-scope", "bigop-binder", "noncomputable-thm",
        "missing-import", "bad-dot-notation", "unfold-absent"}


def src(m):
    return os.path.join(ROOT, m.replace(".", os.sep) + ".lean")


def olean(m):
    return os.path.join(BUILD, m.replace(".", os.sep) + ".olean")


def lean_env():
    env = dict(os.environ)
    roots = []
    if CACHE and os.path.isdir(CACHE):
        for n in sorted(os.listdir(CACHE)):
            d = os.path.join(CACHE, n, ".lake", "build", "lib", "lean")
            if os.path.isdir(d):
                roots.append(d)
    roots.append(BUILD)
    env["LEAN_PATH"] = ":".join(roots)
    return env


def elaborate(m, env):
    r = subprocess.run(["lean", src(m)], capture_output=True, text=True, env=env)
    return (r.stdout + r.stderr)


def nerrors(out):
    return len(re.findall(r"error", out))


def build_decl_map():
    """name -> set of modules declaring it (for missing-import resolution)."""
    d = defaultdict(set)
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                txt = open(p, encoding="utf-8", errors="replace").read()
                for n in DECL_ANY.findall(txt):
                    d[n.split(".")[-1]].add(mod)
    return d


def import_closure(m, imports, seen=None):
    seen = seen if seen is not None else set()
    for dep in imports.get(m, ()):
        if dep not in seen:
            seen.add(dep)
            import_closure(dep, imports, seen)
    return seen


def all_imports():
    imps = {}
    for dp, _, fs in os.walk(os.path.join(ROOT, "CRNT")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, ROOT)[:-5].replace(os.sep, ".")
                imps[mod] = IMPORT.findall(
                    open(p, encoding="utf-8", errors="replace").read())
    return imps


def classify(out, mod):
    """Return list of (bucket, detail, suggestion)."""
    found = []
    text = open(src(mod), encoding="utf-8", errors="replace").read()
    for line in out.split("\n"):
        if "error" not in line:
            continue
        hit = None
        for bucket, rx, sug in PATTERNS:
            m = re.search(rx, line)
            if m:
                detail = m.group(1) if m.groups() else ""
                # refine: notation-scope only if the bracket is actually used
                if bucket == "notation-scope":
                    if "⟫_ℝ" not in text:
                        continue
                    if "open scoped InnerProductSpace" in text:
                        continue
                hit = (bucket, detail, sug)
                break
        found.append(hit or ("other", line.strip()[:110], "read the diagnostic"))
    # source-level buckets the compiler reports only indirectly
    if re.search(r"∑\s+\w+\s+in\s", text) or re.search(r"∏\s+\w+\s+in\s", text):
        found.append(("bigop-binder", "∑/∏ .. in ..", "use `∈`"))
    if "noncomputable theorem" in text:
        found.append(("noncomputable-thm", "noncomputable theorem", "drop the keyword"))
    return found


def try_fix(mod, buckets, env, declmap, imports):
    """Apply the safe fixes for `mod`. Returns (applied, before, after)."""
    before_out = elaborate(mod, env)
    before = nerrors(before_out)
    if before == 0:
        return [], 0, 0
    path = src(mod)
    orig = open(path, encoding="utf-8").read()
    text = orig
    applied = []

    # 1. bigop binder
    new = re.sub(r"(∑|∏)(\s+\w+(?:\s+\w+)*\s+)in(\s)", r"\1\2∈\3", text)
    if new != text:
        text = new
        applied.append("bigop-binder")

    # 2. noncomputable theorem
    if "noncomputable theorem" in text:
        text = text.replace("noncomputable theorem", "theorem")
        applied.append("noncomputable-thm")

    # 3. notation scope
    if "⟫_ℝ" in text and "open scoped InnerProductSpace" not in text:
        lines = text.split("\n")
        idx = None
        for i, l in enumerate(lines):
            if l.strip() == "namespace CRNT":
                idx = i + 1
                break
        if idx is None:
            cand = [i for i, l in enumerate(lines) if l.startswith("import ")]
            idx = (max(cand) + 1) if cand else 0
        lines.insert(idx, "\nopen scoped InnerProductSpace\n")
        text = "\n".join(lines)
        applied.append("notation-scope")

    # 4. missing import, only when the name resolves to exactly one module
    unresolved = {d for b, d, _ in buckets
                  if b in ("invalid-field", "unknown-ident", "unknown-const") and d}
    if unresolved:
        have = import_closure(mod, imports) | {mod}
        adds = set()
        for name in unresolved:
            owners = declmap.get(name.split(".")[-1], set())
            owners = {o for o in owners if o != mod}
            if len(owners) == 1:
                owner = next(iter(owners))
                if owner not in have and mod not in import_closure(owner, imports):
                    adds.add(owner)
        if adds:
            lines = text.split("\n")
            cand = [i for i, l in enumerate(lines) if l.startswith("import ")]
            if cand:
                at = max(cand) + 1
                lines[at:at] = [f"import {a}" for a in sorted(adds)]
                text = "\n".join(lines)
                applied.append(f"missing-import({','.join(sorted(adds))})")

    # 4b. bad generalized field notation: the function lives in a namespace but takes no
    #     parameter of the receiver's type, so `N.f` / `G.f` cannot resolve.  Lean names the
    #     function, so stripping the receiver is determined by the error.
    badnames = {d for b, d, _ in buckets if b == "bad-dot-notation" and d}
    if badnames:
        newtext = text
        for nm in badnames:
            short = nm.split(".")[-1]
            newtext = re.sub(r"\b[A-Za-z_][A-Za-z0-9_']*\.(" + re.escape(short) + r")\b",
                             r"\1", newtext)
        if newtext != text:
            text = newtext
            applied.append("bad-dot-notation")

    # 4c. `unfold A B at h ⊢` fails when either location lacks one of the names, while
    #     `simp only [A, B] at h ⊢` tolerates absence.  Pure textual substitution.
    if any(b == "unfold-absent" for b, _, _ in buckets):
        def _unfold_to_simp(m):
            names = m.group(1).split()
            return "simp only [" + ", ".join(names) + "] at " + m.group(2)
        newtext = re.sub(r"unfold\s+([A-Za-z_][\w.']*(?:\s+[A-Za-z_][\w.']*)+)\s+at\s+([\w'\s⊢]+)",
                         _unfold_to_simp, text)
        if newtext != text:
            text = newtext
            applied.append("unfold-absent")

    # 5. noncomputable defs — Lean gives the line number
    nc_lines = sorted({int(m.group(1)) for m in
                       re.finditer(r":(\d+):\d+: error\(lean\.dependsOnNoncomputable\)",
                                   before_out)}, reverse=True)
    if nc_lines:
        lines = text.split("\n")
        changed = False
        for ln in nc_lines:
            if 0 < ln <= len(lines):
                l = lines[ln - 1]
                if re.match(r"^\s*def ", l) and "noncomputable" not in l:
                    lines[ln - 1] = re.sub(r"^(\s*)def ", r"\1noncomputable def ", l)
                    changed = True
        if changed:
            text = "\n".join(lines)
            applied.append("noncomputable")

    if not applied:
        return [], before, before

    open(path, "w", encoding="utf-8").write(text)
    after = nerrors(elaborate(mod, env))
    if after >= before:
        open(path, "w", encoding="utf-8").write(orig)   # no improvement -> revert
        return [], before, before
    return applied, before, after


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--targets")
    ap.add_argument("--module")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--budget", type=float, default=230.0)
    a = ap.parse_args()

    if a.module:
        mods = [a.module]
    elif a.targets:
        mods = [l.strip() for l in open(a.targets)
                if l.strip() and not l.startswith("#")]
    else:
        print("need --targets or --module")
        return 1

    env = lean_env()
    imports = all_imports()
    declmap = build_decl_map() if a.apply else {}

    t0 = time.time()
    tally = defaultdict(int)
    modbuckets = {}
    fixed = []
    scanned = 0

    for m in mods:
        if time.time() - t0 > a.budget:
            print(f"-- budget reached after {scanned} module(s); rerun to continue")
            break
        if not os.path.exists(src(m)):
            continue
        # a module whose deps are unbuilt cannot be judged
        if any(not os.path.exists(olean(d)) for d in imports.get(m, ())):
            tally["blocked-unbuilt-dep"] += 1
            continue
        out = elaborate(m, env)
        scanned += 1
        if nerrors(out) == 0:
            tally["clean"] += 1
            continue
        b = classify(out, m)
        modbuckets[m] = b
        for bucket, _, _ in b:
            tally[bucket] += 1
        if a.apply:
            applied, before, after = try_fix(m, b, env, declmap, imports)
            if applied:
                fixed.append((m, before, after, applied))
                print(f"FIXED {m}: {before} -> {after} errors  [{', '.join(applied)}]")

    print("\n=== defect buckets (by diagnostic count) ===")
    for k, v in sorted(tally.items(), key=lambda kv: -kv[1]):
        mark = " *AUTO*" if k in AUTO else ""
        print(f"{v:>5}  {k}{mark}")

    print(f"\nscanned {scanned} module(s), {len(modbuckets)} failing")
    if a.apply:
        tot_b = sum(b for _, b, _, _ in fixed)
        tot_a = sum(x for _, _, x, _ in fixed)
        print(f"auto-fixed {len(fixed)} module(s): {tot_b} -> {tot_a} errors")
    else:
        print("\ntop failing modules:")
        for m, b in sorted(modbuckets.items(), key=lambda kv: -len(kv[1]))[:15]:
            kinds = ", ".join(sorted({x[0] for x in b}))
            print(f"  {len(b):>3} err  {m}  [{kinds}]")
    return 0


if __name__ == "__main__":
    sys.exit(main())

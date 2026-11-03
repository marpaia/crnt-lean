"""Enforce the invariants around the unverified-module ledger.

Six checks.  Checks 1-4 are the original four; 5 and 6 replace a coverage gap in them.

  1. `lakefile.toml`, `CRNTFrontier.lean` and `scripts/frontier_history.txt` are
     exactly what `gen_lakefile.py --check` would produce from the ledger, so
     nobody can quietly exclude a module by editing a generated file.  This is
     read-only; it never repairs the tree.
  2. The ledger has not grown past its recorded baseline.  It may shrink freely.
  3. Every ledger entry names a file that exists on disk (a stale entry hides the
     fact that a module was deleted -- the previous lakefile excluded
     `CRNT.Decision.StrictConeRealization`, which had no file at all).
  4. `CRNT.lean` does not reach any ledger module, transitively.
  5. `CRNT.lean` does not reach any module carrying a `sorry`/`axiom`/`admit` --
     asserted DIRECTLY on the import closure, not as an intersection with the ledger.
  6. Every `CRNT/` module is accounted for: in the ledger, or in the closure, or
     explicitly noted as glob-only. `Scaffold/` must be covered by the `Scaffold.+` target.

WHY 5 EXISTS.  Check 4 has been vacuous since the ledger was emptied at c56739b:
`set(ledger) & closure` is `set() & anything` == `set()`, so it cannot fail and its
"ok" line is not evidence.  `adv-audit` found this and measured the coverage gap it
conceals: 846 `CRNT/` modules on disk, 701 in `CRNT.lean`'s closure, ledger 0, so 145
modules are covered by no ledger invariant -- and both holes are among them.  Check 5
states the fact check 4 was standing in for, in a form that stays meaningful when the
ledger is empty.  Check 4 is kept because it goes live the moment a module is listed.

Usage:
    python3 scripts/check_exclusions.py
    python3 scripts/check_exclusions.py --coverage          # full census, exit 0
    python3 scripts/check_exclusions.py --write-baseline
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
BASELINE = os.path.join(ROOT, "scripts", "unverified_baseline.txt")
GEN = os.path.join(ROOT, "scripts", "gen_lakefile.py")


def read_ledger() -> list[str]:
    with open(LEDGER, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]


def module_path(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def transitive_imports(entry: str) -> set[str]:
    seen: set[str] = set()
    stack = [entry]
    imp = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
    while stack:
        path = stack.pop()
        full = os.path.join(ROOT, path)
        if not os.path.exists(full):
            continue
        with open(full, encoding="utf-8", errors="replace") as fh:
            for mod in imp.findall(fh.read()):
                if mod not in seen:
                    seen.add(mod)
                    stack.append(mod.replace(".", os.sep) + ".lean")
    return seen

def _modules_under(subdir: str) -> set[str]:
    """Dotted module names of every `.lean` file under `ROOT/subdir`."""
    out = set()
    top = os.path.join(ROOT, subdir)
    if not os.path.isdir(top):
        return out
    for dp, _dirs, files in os.walk(top):
        for f in files:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), ROOT)
            out.add(rel[: -len(".lean")].replace(os.sep, "."))
    return out


def crnt_modules() -> set[str]:
    return _modules_under("CRNT")


def scaffold_modules() -> set[str]:
    return _modules_under("Scaffold")


def scaffold_target_covers_all() -> bool:
    with open(os.path.join(ROOT, "lakefile.toml"), "rb") as fh:
        config = tomllib.load(fh)
    return any(
        lib.get("name") == "Scaffold"
        and "Scaffold.+" in lib.get("globs", [])
        and not lib.get("excludeGlobs", [])
        for lib in config.get("lean_lib", [])
    )


CRNT_MODULES = crnt_modules()


def hole_modules() -> set[str]:
    """`CRNT/` modules whose source carries a `sorry`, `axiom` or `admit`.

    Syntactic and comment-stripped, deliberately: it is a *reachability* check, so a
    false negative (missing a hole) is the failure that matters, and the patterns are
    the conservative superset already baselined by `scripts/check_stubs.py`.  The
    baseline pins exact occurrences; this only has to answer "is this module suspect",
    which is why it is coarser.
    """
    pats = [re.compile(r"(?<!\`)\bsorry\b(?!\`)"),
            re.compile(r"(?<!\`)\badmit\b(?!\`)"),
            # re.M is load-bearing: this scans whole files, so `^` must mean
            # "start of a line".  Without it the pattern can only match at offset 0
            # and never fires -- which is exactly what happened on the first attempt.
            re.compile(r"^[\s]*axiom[\s]+[A-Za-z_]", re.M)]
    block = re.compile(r"/-.*?-/", re.S)
    out = set()
    for mod in CRNT_MODULES:
        path = os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                text = block.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), fh.read())
        except OSError:
            continue
        text = re.sub(r"--.*$", "", text, flags=re.M)
        if any(p.search(text) for p in pats):
            out.add(mod)
    return out



def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-baseline", action="store_true")
    ap.add_argument("--coverage", action="store_true",
                    help="print the full build-target coverage census and exit 0")
    args = ap.parse_args()

    ledger = read_ledger()
    if args.coverage:
        ledger_set = set(ledger)
        reachable = transitive_imports("CRNT.lean")
        on_disk = CRNT_MODULES
        unproved = hole_modules()
        buckets = {
            "in the ledger": sorted(ledger_set & on_disk),
            "reachable from CRNT.lean": sorted(reachable & on_disk - ledger_set),
            "built only by the CRNT.+ glob": sorted(on_disk - ledger_set - reachable),
        }
        print("build-target coverage census")
        print("----------------------------")
        for label, mods in buckets.items():
            sus = [m for m in mods if m in unproved]
            print(f"  {len(mods):4d}  {label}" + (f"   ({len(sus)} carrying a hole)" if sus else ""))
        print(f"  {len(on_disk):4d}  CRNT/ modules on disk")
        orphans = sorted(m for mods in buckets.values() for m in mods if m in unproved)
        if orphans:
            print("\nmodules carrying a sorry/axiom/admit, by bucket:")
            for m in orphans:
                where = next(k for k, v in buckets.items() if m in v)
                print(f"  {m}  [{where}]")
        sc = scaffold_modules()
        target = "covered by Scaffold.+" if scaffold_target_covers_all() else "NOT covered by Scaffold.+"
        print(f"\n  {len(sc):4d}  Scaffold/ modules -- {target}")
        for m in sorted(sc):
            print(f"          {m}")
        return 0

    if args.write_baseline:
        with open(BASELINE, encoding="utf-8", mode="w") as fh:
            fh.write("# High-water mark for scripts/unverified_modules.txt.\n")
            fh.write("# The ledger may shrink below this number, never grow above it.\n")
            fh.write(f"{len(ledger)}\n")
        print(f"baseline set to {len(ledger)}")
        return 0

    failed = False

    # ---- 1. generated files in sync -----------------------------------------
    # `--check` writes nothing.  The previous version regenerated the lakefile as a
    # side effect of *testing* it, so a gate could silently repair a hand-edited
    # lakefile and then report "ok" -- the drift was fixed locally and merged as a
    # no-op, and the next checkout broke again.
    proc = subprocess.run([sys.executable, GEN, "--check"], capture_output=True, text=True)
    if proc.returncode != 0:
        failed = True
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        print("::error::generated files drifted from scripts/unverified_modules.txt "
              "(run `python3 scripts/gen_lakefile.py` and commit the result).", file=sys.stderr)
    else:
        print(proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else
              "ok: lakefile.toml matches the ledger")

    # ---- 2. shrink-only -----------------------------------------------------
    if os.path.exists(BASELINE):
        with open(BASELINE, encoding="utf-8") as fh:
            nums = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
        high = int(nums[0])
        if len(ledger) > high:
            failed = True
            print(f"::error::unverified-module ledger grew from {high} to {len(ledger)}. "
                  f"New modules must build, or the growth must be justified and the "
                  f"baseline raised deliberately.", file=sys.stderr)
        else:
            print(f"ok: ledger at {len(ledger)} modules (baseline {high})")
    else:
        print("warning: no baseline; run --write-baseline", file=sys.stderr)

    # ---- 3. no stale entries ------------------------------------------------
    stale = [m for m in ledger if not os.path.exists(module_path(m))]
    if stale:
        failed = True
        print("::error::ledger entries with no file on disk:", file=sys.stderr)
        for m in stale:
            print(f"  {m}", file=sys.stderr)
    else:
        print(f"ok: all {len(ledger)} ledger entries exist on disk")

    # ---- 4. core does not depend on the frontier ----------------------------
    # The ledger form of this check is VACUOUS while the ledger is empty: `set() &
    # anything` is `set()`, so it cannot fail, and its "ok" line is not evidence of
    # anything.  Measured: ledger 0, closure 701, intersection 0.  It is kept because
    # it becomes live the moment a module is listed, and it is cheap -- but it is NOT
    # the check that protects the core, and check 5 below is.
    reachable = transitive_imports("CRNT.lean")
    leaked = sorted(set(ledger) & reachable)
    if leaked:
        failed = True
        print("::error::CRNT.lean transitively imports unverified modules:", file=sys.stderr)
        for m in leaked:
            print(f"  {m}", file=sys.stderr)
    else:
        print(f"ok: the verified core reaches none of the {len(ledger)} ledger module(s)"
              + ("  [vacuous: the ledger is empty -- see check 5]"
                 if not ledger else ""))

    # ---- 5. the verified core carries no hole, checked DIRECTLY -------------
    # This is the invariant check 4 was standing in for.  It is asserted on the
    # closure itself rather than as an intersection with the ledger, so it stays
    # meaningful when the ledger is empty -- which is the state it has been in since
    # commit c56739b, i.e. check 4 has never actually run as a check.
    #
    # It also closes the coverage gap `adv-audit` named: 145 `CRNT/` modules are
    # neither in the ledger nor reachable from `CRNT.lean` (846 on disk, 701 in the
    # closure, ledger 0).  Both holes are among the 145, so no ledger invariant
    # covered them.  That is a gap in *coverage*, not accuracy -- every one of the 145
    # elaborates, and check_stubs' shrink-only baseline pins the two `sorry`s.  But a
    # new `sorry` in a module that later joins the umbrella has to be caught by
    # something, and this is it.
    unproved = hole_modules()
    holes_in_core = sorted(unproved & reachable)
    if holes_in_core:
        failed = True
        print("::error::`import CRNT` reaches modules carrying a sorry/axiom/admit. "
              "The verified core cannot depend on unproved source:", file=sys.stderr)
        for m in holes_in_core:
            print(f"  {m}", file=sys.stderr)
        print("  Drop them from CRNT.lean, or prove them.", file=sys.stderr)
    else:
        print(f"ok: none of the {len(unproved)} module(s) carrying a sorry/axiom/admit "
              f"is reachable from `import CRNT`  (closure {len(reachable)}, "
              f"{len(CRNT_MODULES)} modules on disk)")

    # ---- 6. every CRNT/ module is in some build target ----------------------
    # The 145 are built by the `CRNT.+` glob, so they are not lost -- but nothing
    # *stated* that, and the only thing that would catch one silently leaving every
    # target is a check that no module is in no target. Scaffolds have a separate
    # blanket glob so new scaffolds cannot silently escape elaboration either.
    on_disk = set(crnt_modules())
    covered = (set(ledger) | reachable) & on_disk
    uncovered = sorted(on_disk - covered)
    if uncovered:
        print(f"note: {len(uncovered)} CRNT/ module(s) are in neither the ledger nor "
              f"`CRNT.lean`'s closure; they are built by the CRNT.+ glob and pinned by "
              f"scripts/stub_baseline.txt. Run --coverage for the list.")
    else:
        print("ok: every CRNT/ module is either in the ledger or reachable from CRNT.lean")

    scaffold = scaffold_modules()
    if scaffold:
        if scaffold_target_covers_all():
            print(f"ok: all {len(scaffold)} Scaffold/ module(s) are covered by Scaffold.+")
        else:
            print("::error::Scaffold/ modules must be covered by the Scaffold.+ target",
                  file=sys.stderr)
            failed = True

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Generate `lakefile.toml` and `CRNTFrontier.lean` from the exclusion ledger.

The only file a human edits is `scripts/unverified_modules.txt` (the *ledger*):
the list of modules Lean has never elaborated.  Two targets are derived from it:

    CRNT           everything under CRNT/ except the ledger  -- must build green
    CRNTFrontier   the ledger, plus every module the ledger has *ever* held
                   -- must build green

Scaffold.+ and every Lean test module are included in separate required targets.

Two lists, not one, and the second one matters.  The original lakefile enumerated
the 449 verified modules by name, so a new file was silently left out of the build
unless someone remembered to add it; inverting that to a `CRNT.+` glob fixed the
common case but created a second one: a module that graduates out of the ledger
used to *disappear* from the frontier, so CI's error count quietly stopped
measuring it.  `scripts/frontier_history.txt` is the append-only record of every
module the frontier target has ever covered, and `CRNTFrontier.lean` is generated
from `ledger ∪ history` -- so a module can leave the ledger but never leaves the
build, and the frontier metric stays monotone.

Because Lake's globs are hierarchical (`excludeGlobs = ["CRNT.Foo"]` silently
drops every `CRNT.Foo.*` too), this script also refuses to write when a ledger
entry would transitively exclude a module that is not itself on the ledger: that
is the one way a newly added `CRNT/` file can still vanish from every target.

Usage
-----
    python3 scripts/gen_lakefile.py                 # regenerate both files
    python3 scripts/gen_lakefile.py --check         # CI: exit 1 if either is stale
    python3 scripts/gen_lakefile.py --add MODULE    # add an unelaborated module
    python3 scripts/gen_lakefile.py --remove MODULE # retire one into history
    python3 scripts/gen_lakefile.py --print         # dump the frontier set

Every write mode is atomic: content is computed first, validated, and only then
written, so a validation failure never leaves a half-generated tree behind.
"""

from __future__ import annotations

import argparse
import difflib
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "scripts", "unverified_modules.txt")
HISTORY = os.path.join(ROOT, "scripts", "frontier_history.txt")
LAKEFILE = os.path.join(ROOT, "lakefile.toml")
FRONTIER = os.path.join(ROOT, "CRNTFrontier.lean")

MATHLIB_REV = "v4.34.0"

HISTORY_HEADER = """\
# Every module the CRNTFrontier target has ever covered -- append-only.
#
# The active frontier is `scripts/unverified_modules.txt` plus this list.  When a
# module graduates out of the ledger (it elaborates, so it belongs in the verified
# `CRNT` target) it is appended here rather than forgotten, so that `lake build
# CRNTFrontier` keeps elaborating it and CI's frontier error count keeps measuring
# it.  `scripts/gen_lakefile.py` maintains this file; edit the ledger, not this.
"""


# --------------------------------------------------------------------------- io


def read_entries(path: str) -> list[str]:
    """Non-comment, non-blank lines of a ledger-style file."""
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as fh:
        return [ln.strip() for ln in fh if ln.strip() and not ln.lstrip().startswith("#")]


def module_path(mod: str) -> str:
    return os.path.join(ROOT, mod.replace(".", os.sep) + ".lean")


def all_crnt_modules() -> list[str]:
    out = []
    top = os.path.join(ROOT, "CRNT")
    for dp, _, fs in os.walk(top):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), ROOT)
            out.append(rel[: -len(".lean")].replace(os.sep, "."))
    return sorted(out)


def test_globs() -> list[str]:
    """Every `test/` module, including the frontier audits and negative controls.

    Lake does not honour `excludeGlobs` on this library -- a module listed there is still
    elaborated (verified by patching the key, both as `excludeGlobs` and `exclude_globs`,
    and watching the module still be built).  The exclusion therefore has to be expressed by
    what the glob enumerates.  Scanning the directory rather than hard-coding the list keeps
    the original property: a newly added test file is in the build by default.
    """
    out = []
    for base, _, files in os.walk(os.path.join(ROOT, "test")):
        for name in files:
            if name.endswith(".lean"):
                rel = os.path.relpath(os.path.join(base, name), ROOT)
                out.append(rel[:-len(".lean")].replace(os.sep, "."))
    return sorted(out)


# ------------------------------------------------------------------- validation


def validate(ledger: list[str], history: list[str]) -> list[str]:
    """Every way a `CRNT/` module could fail to be in *any* build target.

    Returns a list of human-readable problems; empty means the configuration is
    sound.  Called before anything is written, in both `--check` and write mode.
    """
    problems: list[str] = []

    dupes = sorted({m for m in ledger if ledger.count(m) > 1})
    if dupes:
        problems.append(f"ledger lists these modules more than once: {', '.join(dupes)}")

    stale = [m for m in ledger if not os.path.exists(module_path(m))]
    if stale:
        problems.append(
            "ledger entries with no file on disk (a stale entry hides that the module was "
            f"deleted): {', '.join(sorted(stale))}"
        )

    stale_hist = [m for m in history if not os.path.exists(module_path(m))]
    if stale_hist:
        problems.append(
            "frontier-history entries with no file on disk: " f"{', '.join(sorted(stale_hist))}"
        )

    # Lake globs are hierarchical: excluding `CRNT.Foo` also excludes `CRNT.Foo.Bar`.
    # A submodule hidden that way is dropped from the `CRNT` target *and* is not on
    # the frontier target unless it is listed in its own right -- i.e. it is in no
    # build at all.  That is the silent-exclusion hole; make each one explicit.
    on_disk = set(all_crnt_modules())
    ledger_set = set(ledger)
    hidden: dict[str, str] = {}
    for entry in ledger:
        prefix = entry + "."
        for mod in on_disk:
            if mod.startswith(prefix) and mod not in ledger_set:
                hidden.setdefault(mod, entry)
    if hidden:
        problems.append(
            "these CRNT/ files are excluded transitively by a ledger entry but are not on the "
            "frontier target, so no build elaborates them -- list each one in "
            "scripts/unverified_modules.txt (or narrow the entry): "
            + ", ".join(f"{m} (hidden by {e})" for m, e in sorted(hidden.items()))
        )

    # A module in history but no longer on disk would make `lake build CRNTFrontier`
    # fail for a reason that has nothing to do with the frontier.
    return problems


# --------------------------------------------------------------------- rendering


def toml_list(items: list[str], indent: int = 2) -> str:
    if not items:
        return "[]"
    pad = " " * indent
    body = ",\n".join(f'{pad}"{i}"' for i in items)
    return "[\n" + body + "\n]"


def render_lakefile(ledger: list[str], frontier: list[str], tests: list[str]) -> str:
    return f"""# GENERATED by scripts/gen_lakefile.py -- do not edit by hand.
# The single source of truth for what is and is not verified is
# scripts/unverified_modules.txt.  Edit that, then regenerate.

name = "crnt-lean"
defaultTargets = ["CRNT"]
testRunner = "test"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{MATHLIB_REV}"

# The verified core: everything under CRNT/ except the ledger.  Globbing by pattern
# (rather than enumerating modules) means a newly added file is in the build by default
# and has to be deliberately excluded, not the other way round.
[[lean_lib]]
name = "CRNT"
globs = ["CRNT", "CRNT.+"]
excludeGlobs = {toml_list(ledger)}

# The frontier: the ledger plus everything the frontier target has ever covered
# (scripts/frontier_history.txt).  `CRNTFrontier.lean` is generated from the same set,
# so a module that graduates out of the ledger is elaborated here instead of quietly
# dropping out of build coverage. CI requires this target to elaborate successfully.
[[lean_lib]]
name = "CRNTFrontier"
globs = {toml_list(frontier)}

# Research scaffolds are checked for elaboration independently of the public umbrella.
[[lean_lib]]
name = "Scaffold"
globs = ["Scaffold.+"]

[[lean_lib]]
name = "test"
globs = {toml_list(tests)}

[[lean_exe]]
name = "analyze"
root = "Analyze"
"""


def render_frontier(frontier: list[str], ledger: list[str]) -> str:
    live = set(ledger)
    imports = "\n".join(f"import {m}" for m in frontier)
    note = (
        f"{len(frontier)} modules: every one the frontier target has ever covered, of which "
        f"{len(live)} are still unverified and on scripts/unverified_modules.txt"
        if frontier
        else "empty: the frontier target has never covered a module"
    )
    return f"""-- GENERATED by scripts/gen_lakefile.py -- do not edit by hand.
-- Frontier aggregator: {note}.
-- To change it, edit scripts/unverified_modules.txt and re-run
-- `python3 scripts/gen_lakefile.py`.

{imports}

/-!
# Frontier aggregator.

Every module it imports is elaborated by `lake build CRNTFrontier`, including the
ones that have graduated into the verified `CRNT` target -- that is what makes the
coverage independent of which modules happen to be unverified today. CI requires
this target to build successfully.
-/
"""


# ----------------------------------------------------------------------- writing


def read_text(path: str) -> str:
    if not os.path.exists(path):
        return ""
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def write_if_changed(path: str, text: str, check: bool) -> bool:
    """Write `text` to `path`.  Returns True if the file was already correct."""
    if read_text(path) == text:
        return True
    if not check:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(text)
    return False


def diff(path: str, text: str) -> str:
    return "".join(
        difflib.unified_diff(
            read_text(path).splitlines(keepends=True),
            text.splitlines(keepends=True),
            fromfile=f"a/{os.path.relpath(path, ROOT)}",
            tofile=f"b/{os.path.relpath(path, ROOT)}",
        )
    )


def sync_history(ledger: list[str], history: list[str], check: bool) -> list[str]:
    """Return the post-sync history, writing it unless `check`.

    A module that leaves the ledger is appended, never dropped: that append is what
    keeps `lake build CRNTFrontier` covering it after it graduates.
    """
    seen = set(history)
    return history + [m for m in ledger if m not in seen]


def render_history(history: list[str]) -> str:
    return HISTORY_HEADER + "\n" + "\n".join(sorted(set(history))) + ("\n" if history else "")


def edit_ledger(action: str, mod: str) -> int:
    """`--add` / `--remove` a single ledger entry, preserving the comment header."""
    lines = read_text(LEDGER).split("\n")
    entries = read_entries(LEDGER)
    if action == "add":
        if mod in entries:
            print(f"{mod} is already on the ledger")
            return 0
        if not os.path.exists(module_path(mod)):
            print(f"::error::no file at {os.path.relpath(module_path(mod), ROOT)}", file=sys.stderr)
            return 1
        at = len(lines)
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip() and not lines[i].lstrip().startswith("#"):
                at = i + 1
                break
        lines[at:at] = [mod]
    else:
        if mod not in entries:
            print(f"{mod} is not on the ledger (nothing to remove)")
            return 0
        lines = [ln for ln in lines if ln.strip() != mod]
        # Collapse the blank line an entry removal can leave behind.
        lines = [ln for i, ln in enumerate(lines) if not (ln == "" and lines[i - 1:i] == [""])]
    with open(LEDGER, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines))
    print(f"ledger: {action} {mod}")
    return 0


# -------------------------------------------------------------------------- main


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true", help="verify without writing; exit 1 if stale")
    ap.add_argument("--add", metavar="MODULE", help="add an unelaborated module to the ledger")
    ap.add_argument("--remove", metavar="MODULE", help="retire a module out of the ledger")
    ap.add_argument("--print", dest="show", action="store_true", help="print the frontier set")
    args = ap.parse_args()

    if args.add or args.remove:
        if args.add and args.remove:
            ap.error("--add and --remove are mutually exclusive")
        rc = edit_ledger("add" if args.add else "remove", args.add or args.remove)
        if rc:
            return rc

    ledger = read_entries(LEDGER)
    history = sync_history(ledger, read_entries(HISTORY), args.check)

    problems = validate(ledger, history)
    if problems:
        for p in problems:
            print("::error::" + p, file=sys.stderr)
        print(f"::error::refusing to write a lakefile that would hide modules "
              f"({len(problems)} problem(s)); ledger left unchanged", file=sys.stderr)
        return 1

    frontier = sorted(set(ledger) | set(history))
    tests = test_globs()

    if args.show:
        for m in frontier:
            print(m)
        return 0

    lake_text = render_lakefile(ledger, ["CRNTFrontier"] + frontier, tests)
    frontier_text = render_frontier(frontier, ledger)
    history_text = render_history(history)

    stale = []
    if not write_if_changed(LAKEFILE, lake_text, args.check):
        stale.append("lakefile.toml")
    if not write_if_changed(FRONTIER, frontier_text, args.check):
        stale.append("CRNTFrontier.lean")
    if not write_if_changed(HISTORY, history_text, args.check):
        stale.append("scripts/frontier_history.txt")

    if args.check:
        if stale:
            print("::error::generated files are out of sync with scripts/unverified_modules.txt: "
                  + ", ".join(stale), file=sys.stderr)
            for path, text in (
                (LAKEFILE, lake_text),
                (FRONTIER, frontier_text),
                (HISTORY, history_text),
            ):
                if read_text(path) != text:
                    sys.stderr.write(diff(path, text))
            print("::error::run `python3 scripts/gen_lakefile.py` and commit the result",
                  file=sys.stderr)
            return 1
        print(f"ok: lakefile.toml, CRNTFrontier.lean and frontier_history.txt all in sync "
              f"({len(ledger)} excluded, {len(frontier)} on the frontier, "
              f"{len(tests)} test module(s) built, no test exclusions)")
        return 0

    print(f"wrote lakefile.toml: {len(ledger)} excluded from CRNT, "
          f"{len(frontier)} in CRNTFrontier "
          f"({len(frontier) - len(ledger)} graduated), "
          f"{len(tests)} test module(s) built, no test exclusions")
    return 0


if __name__ == "__main__":
    sys.exit(main())

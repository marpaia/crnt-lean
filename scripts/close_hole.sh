#!/usr/bin/env bash
# close_hole.sh — certify one closed hole and reconcile the whole tree, in one command.
#
#   scripts/close_hole.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean \
#       Network.exists_positive_omegaPoint_of_highCodimension_siphonFace
#
# Closing a hole is not one edit, it is a reconciliation of six things that are only
# correct together, and doing it by hand in the wrong order is how a merge lands green
# locally and red in CI:
#
#   1. the affected modules elaborate, in dependency order;
#   2. the named theorem's axiom set is a subset of {propext, Classical.choice, Quot.sound};
#   3. `scripts/dump_sorries.py` agrees that the hole is gone;
#   4. `scripts/unverified_modules.txt` no longer lists the module;
#   5. the generated files (lakefile.toml, CRNTFrontier.lean, frontier history) match it,
#      and the four static gates are green;
#   6. `lake build CRNT` is green.
#
# This runs all six and prints one PASS/FAIL summary.  It is **transactional**: it
# snapshots every file it may touch and restores the snapshot on any failure, so a failed
# run leaves the ledger, the lakefile and `CRNT.lean` exactly as they were.  Nothing is
# committed -- review the diff and commit it yourself.
#
# Options
#   --no-build   skip step 6's full `lake build CRNT`.  Agents must use this: a full build
#                from a researcher's worktree destroys the round for everyone.  A run with
#                --no-build does NOT certify the full build and says so in its summary.
#   --all-deps   re-elaborate the whole transitive CRNT import closure, not just the parts
#                of it that are not already built.
#
# Environment
#   MAX_REBUILD (default 32)  cap on step 1.  When more modules than this need
#     elaborating the shared build cache has fallen behind the branch, and rebuilding
#     is a full build -- the orchestrator's job, not this command's.
#
# Exit 0 = every step passed.  Exit 1 = something failed and the tree was restored.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

PY="${PYTHON:-python3}"
CHECKMOD="$ROOT/research/scripts/checkmod.sh"
SKIP_BUILD=0
ALL_DEPS=0

MAX_REBUILD="${MAX_REBUILD:-32}"
POSITIONAL=""

for arg in "$@"; do
  case "$arg" in
    --no-build) SKIP_BUILD=1 ;;
    --all-deps) ALL_DEPS=1 ;;
    -h|--help) sed -n '2,32p' "$0"; exit 0 ;;
    -*) echo "unknown option: $arg" >&2; exit 2 ;;
    *) POSITIONAL="$POSITIONAL $arg" ;;
  esac
done

set -- $POSITIONAL
if [ "$#" -ne 2 ]; then
  echo "usage: scripts/close_hole.sh [--no-build] [--all-deps] <Module.lean> <TheoremName>" >&2
  exit 2
fi
MODULE_PATH="$1"
THEOREM="$2"
MODULE="$(printf '%s' "${MODULE_PATH%.lean}" | tr '/' '.')"

LEDGER="scripts/unverified_modules.txt"
BASELINE="scripts/unverified_baseline.txt"
HISTORY="scripts/frontier_history.txt"
UMBRELLA="CRNT.lean"
TOUCHED="$LEDGER $BASELINE $HISTORY $UMBRELLA lakefile.toml CRNTFrontier.lean"

SNAP=""
FAILED=0
STEPS=""
TMP="$(mktemp -d)"

step() { printf '\n=== %s\n' "$1"; }
record() { STEPS="$STEPS$(printf '%s|%s' "$1" "$2")
"; }
fail() { printf '  -> FAIL: %s\n' "$1" >&2; record "${2:-step}" "FAIL"; FAILED=1; }
ledger_count() { grep -cv '^[[:space:]]*#\|^[[:space:]]*$' "$1" 2>/dev/null || true; }

restore() {
  printf '\n--- rolling back ---\n' >&2
  for rel in $TOUCHED; do
    if [ -f "$SNAP/$rel" ]; then
      mkdir -p "$(dirname "$rel")"
      cp "$SNAP/$rel" "$rel"
      printf '  restored %s\n' "$rel" >&2
    elif [ -e "$rel" ]; then
      rm -f "$rel"
      printf '  removed %s (did not exist before this run)\n' "$rel" >&2
    fi
  done
}

cleanup() {
  if [ "$FAILED" -ne 0 ]; then
    [ -n "$SNAP" ] && restore
    rm -rf "$TMP"
    printf '\n===== close_hole.sh: FAIL (tree restored) =====\n'
    exit 1
  fi
  rm -rf "$TMP"
  printf '\n===== close_hole.sh: PASS =====\n'
  exit 0
}
trap cleanup EXIT

# ------------------------------------------------------------------ 0. preflight

SNAP="$TMP/snap"
for rel in $TOUCHED; do
  mkdir -p "$SNAP/$(dirname "$rel")"
  [ -f "$rel" ] && cp "$rel" "$SNAP/$rel"
done

step "0. preflight"
if [ ! -f "$MODULE_PATH" ]; then
  fail "no such file: $MODULE_PATH" "preflight"
  exit 1
fi
printf '  module : %s\n  theorem: %s\n' "$MODULE" "$THEOREM"
if ! grep -Eq "(theorem|lemma)[[:space:]]+${THEOREM}([^A-Za-z0-9_']|$)" "$MODULE_PATH"; then
  fail "$THEOREM is not declared in $MODULE_PATH" "preflight"
  exit 1
fi
record "preflight" "PASS"

# --------------------------------------------- 1. rebuild, in dependency order

step "1. rebuild affected modules in dependency order"
SHARED="${CRNT_ROOT:-/Users/akutuva/Documents/Proofs/crnt-lean}"
# Sources that actually differ from HEAD (edited, or not yet committed).  Only these
# can force a rebuild; everything else is already reflected in an existing olean.
TOUCHED_SRC="$({ git diff --name-only HEAD -- CRNT Scaffold; git ls-files --others \
    --exclude-standard -- CRNT Scaffold; } 2>/dev/null | sort -u | tr '\n' ' ')"
ORDER="$("$PY" - "$MODULE" "$ALL_DEPS" "$ROOT" "$SHARED" "$TOUCHED_SRC" <<'PYEOF'
import os, re, sys

mod, all_deps, root = sys.argv[1], sys.argv[2] == "1", sys.argv[3]
shared = sys.argv[4] if len(sys.argv) > 4 else "/Users/akutuva/Documents/Proofs/crnt-lean"
touched = set(sys.argv[5].split()) if len(sys.argv) > 5 else set()
imp = re.compile(r"^import\s+(CRNT[\w.]*)", re.M)
builds = [os.path.join(root, ".lake", "build", "lib", "lean"),
          os.path.join(shared, ".lake", "build", "lib", "lean")]
cache = {}


def deps(m):
    if m not in cache:
        p = os.path.join(root, m.replace(".", os.sep) + ".lean")
        cache[m] = (imp.findall(open(p, encoding="utf-8", errors="replace").read())
                    if os.path.exists(p) else [])
    return cache[m]


def stale(m):
    """Does this module need re-elaborating?

    Wall-clock mtimes are the wrong test on a fresh checkout: every source file is
    newer than every `.olean` in the shared cache, so a tree nobody has touched looks
    entirely stale and this command would re-elaborate hundreds of modules before
    checking anything.  Git knows which sources actually differ from the commit, and
    that is the only thing that should force a rebuild.

    So a module whose source is modified or untracked is stale when the newest olean
    for it predates the edit; a module pristine relative to HEAD is fresh as soon as
    some olean exists, wherever it lives.  The shared cache counts because it is
    exactly what `research/scripts/checkmod.sh` elaborates against.
    """
    rel = m.replace(".", os.sep) + ".lean"
    src = os.path.join(root, rel)
    newest = 0.0
    for b in builds:
        olean = os.path.join(b, m.replace(".", os.sep) + ".olean")
        if os.path.exists(olean):
            newest = max(newest, os.path.getmtime(olean))
    if rel not in touched:
        return newest == 0.0
    return newest == 0.0 or os.path.getmtime(src) > newest


def has_olean(m):
    return any(os.path.exists(os.path.join(b, m.replace(".", os.sep) + ".olean"))
               for b in builds)


order, seen = [], set()


def visit(m):
    if m in seen:
        return
    seen.add(m)
    for d in deps(m):
        visit(d)
    order.append(m)


visit(mod)

# A module cannot be elaborated if anything below it has no olean anywhere.  The
# shared cache lags `holes` whenever the branch has moved since the last full build,
# and then what is missing is a *dependency*, not the target -- without this the
# failure surfaces as a bare "object file ... does not exist" for an unrelated module
# several steps down the import graph.  `order` is post-order, so one forward sweep
# propagates availability upwards.
ok = {}
for m in order:
    ok[m] = has_olean(m) and all(ok.get(d, False) for d in deps(m))

# The module under certification is always re-elaborated, even when git reports it
# pristine and some olean for it exists: step 2 has to *import the current source*, and
# a shared-cache olean built from an older revision would certify a theorem that is not
# the one on disk.
todo = list(dict.fromkeys(order if all_deps else order + [mod]))
for m in todo:
    if m == mod or all_deps or not ok.get(m, False) or stale(m):
        print(m)
PYEOF
)"
if [ $? -ne 0 ]; then
  fail "could not compute the import order" "rebuild"
  exit 1
fi

STALE=""
for m in $ORDER; do STALE="$STALE $m"; done
NSTALE=$(printf '%s\n' $STALE | grep -c . || true)
NTOTAL=$(printf '%s\n' "$ORDER" | grep -c . || true)
printf '  %s module(s) in the transitive closure, %s need elaborating\n' "$NTOTAL" "$NSTALE"

RC=0
if [ "$NSTALE" -eq 0 ]; then
  printf '  nothing to elaborate: every module already has a usable olean\n'
  record "rebuild (0 needed)" "PASS"
elif [ "$NSTALE" -gt "$MAX_REBUILD" ]; then
  # The shared cache has fallen behind the branch.  Rebuilding the closure is then a
  # full build, which is the orchestrator's job and not this command's -- and running
  # it from a researcher's worktree would destroy the round for everyone.  Saying so
  # is the useful output; silently elaborating 162 modules is not.
  printf '  REFUSING: %s modules need elaborating, more than MAX_REBUILD=%s.\n' \
    "$NSTALE" "$MAX_REBUILD"
  printf '  This is what a stale build cache looks like: modules added to the branch\n'
  printf '  since the last `lake build` have no .olean anywhere.  Run `lake build` once\n'
  printf '  (or `lake build %s`) from the integration repo, or raise MAX_REBUILD.\n' "$MODULE"
  fail "shared build cache is behind the branch" "rebuild"
  set -- "$MODULE_PATH" "$THEOREM"
else
  for m in $STALE; do printf '%s\n' "$m"; done > "$TMP/stale"
  set --
  while IFS= read -r m; do set -- "$@" "$(printf '%s' "$m" | tr '.' '/').lean"; done < "$TMP/stale"
  bash "$CHECKMOD" --quiet "$@" || RC=1
  if [ "$RC" -eq 0 ]; then
    for m in $STALE; do printf '  ok %s\n' "$m"; done
    record "rebuild ($NSTALE module(s))" "PASS"
  else
    fail "elaboration failed; first diagnostics above" "rebuild"
  fi
  set -- "$MODULE_PATH" "$THEOREM"
fi

# ------------------------------------------------------ 2. axiom cleanliness

step "2. #print axioms on $THEOREM"
if "$PY" scripts/check_axioms.py "$MODULE_PATH" "$THEOREM"; then
  record "axioms" "PASS"
else
  # Surface the tool's own diagnosis rather than asserting a cause it may not have:
  # "no olean" and "axiom outside the allowed set" are different failures.
  fail "see the check_axioms.py diagnostic above" "axioms"
fi


# ---------------------------------------------------------- 3. sorry inventory

step "3. sorry inventory"
if "$PY" scripts/dump_sorries.py > "$TMP/sorries" 2>&1; then
  printf '  %s\n  %s\n' \
    "$(head -1 "$TMP/sorries")" \
    "$(sed -n 3p "$TMP/sorries")"
  # Match the record itself (`<module>:<line>  [theorem <name>]`), not just the module
  # name: `CRNT.Foo` is a prefix of `CRNT.Foo.Bar`, and a still-open `sorry` somewhere
  # else in the same module is not evidence about this theorem either way.
  if grep -F "$MODULE:" "$TMP/sorries" | grep -qF "$THEOREM"; then
    fail "$THEOREM still carries a sorry" "sorries"
  else
    printf '  %s no longer carries a sorry\n' "$THEOREM"
    record "sorries" "PASS"
  fi
else
  fail "scripts/dump_sorries.py failed" "sorries"
fi

# ------------------------------------------------------- 4. ledger reconciliation

step "4. ledger"
BEFORE_N="$(ledger_count "$LEDGER")"
if "$PY" scripts/gen_lakefile.py --remove "$MODULE"; then
  AFTER_N="$(ledger_count "$LEDGER")"
  printf '  ledger entries: %s -> %s\n' "${BEFORE_N:-0}" "${AFTER_N:-0}"
  # Lowering the growth guard is the one thing no automatic tool may do on its own: the
  # guard is what makes re-adding the same bad modules detectable, and an unverified
  # auto-lowering turns a promotion into an unlimited licence to exclude.  This is the
  # certified path, and the certification is steps 1-3 and 5.
  if [ "${AFTER_N:-0}" -lt "${BEFORE_N:-0}" ]; then
    "$PY" - "$BASELINE" "$AFTER_N" <<'PYEOF'
import sys
with open(sys.argv[1], "w", encoding="utf-8") as fh:
    fh.write("# High-water mark for scripts/unverified_modules.txt.\n")
    fh.write("# The ledger may shrink below this number, never grow above it.\n")
    fh.write(f"{int(sys.argv[2])}\n")
PYEOF
    printf '  lowered the growth guard to %s (certified by steps 1-3 and 5)\n' "$AFTER_N"
  fi
  record "ledger" "PASS"
else
  fail "could not remove $MODULE from $LEDGER" "ledger"
fi

step "5. regenerate lakefile.toml, CRNTFrontier.lean, frontier history"
if "$PY" scripts/gen_lakefile.py && "$PY" scripts/gen_lakefile.py --check; then
  record "generated files" "PASS"
else
  fail "generated files out of sync with the ledger" "generated files"
fi

# --------------------------------------------------------------- 6. static gates

step "6. static gates"
GATE_FAIL=0
for gate in check_imports check_stubs check_undefined_names check_exclusions; do
  out="$("$PY" "scripts/$gate.py" 2>&1)"
  if [ $? -eq 0 ]; then
    printf '  %-24s PASS\n' "$gate"
  else
    printf '  %-24s FAIL\n' "$gate"
    printf '%s\n' "$out" | tail -20 | sed 's/^/    /'
    GATE_FAIL=1
  fi
done
if [ "$GATE_FAIL" -eq 0 ]; then
  record "4 static gates" "PASS"
else
  fail "at least one static gate failed" "4 static gates"
fi

# ----------------------------------------------------------------- 7. full build

step "7. lake build CRNT"
if [ "$SKIP_BUILD" -eq 1 ]; then
  printf '  SKIPPED (--no-build): this run does NOT certify the full build\n'
  record "lake build CRNT" "SKIP"
elif lake build CRNT 2>&1 | tail -30; then
  record "lake build CRNT" "PASS"
else
  fail "lake build CRNT is not green" "lake build CRNT"
fi

# -------------------------------------------------------------------- summary

printf '\n--- summary ---\n'
printf '%s' "$STEPS" | while IFS='|' read -r name verdict; do
  [ -n "$name" ] && printf '  %-34s %s\n' "$name" "$verdict"
done
if [ "$FAILED" -ne 0 ]; then
  printf '\nNot certified; the ledger, the generated files and CRNT.lean have been restored.\n'
else
  printf '\nCertified. Review and commit the diff:\n'
  git --no-pager diff --stat -- $TOUCHED
fi
exit "$FAILED"

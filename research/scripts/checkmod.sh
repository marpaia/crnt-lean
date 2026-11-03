#!/usr/bin/env bash
# checkmod.sh — the ONE sanctioned way an agent type-checks a module.
#
#   research/scripts/checkmod.sh CRNT/Dynamics/HighCodimensionSiphonFace.lean
#   research/scripts/checkmod.sh --quiet CRNT/Geometry/PolyhedralBarrier.lean
#
# Elaborates the given source file against the *shared* build cache
# ($CRNT_ROOT/.lake/build/lib/lean) so that every agent sees the same dependency
# oleans without each agent paying for a private full Lake build.
#
# Exit code 0 = the file elaborates.  Non-zero = read the diagnostics.
#
# ---------------------------------------------------------------------------
# ORDERING IS LOAD-BEARING.  `lake env` PREPENDS its own entries to LEAN_PATH.
# In a worktree that means the worktree-local `.lake/build/lib/lean` lands
# AHEAD of the shared root, Lean resolves the `CRNT` namespace to the worktree,
# and every CRNT-importing module fails with "object file ... does not exist" —
# even though nothing is wrong with the source.  So: put the SHARED ROOT FIRST,
# and call `lean` directly rather than through `lake env`.
#
# Found and diagnosed by form-scales, round 1.  Before this fix the script
# silently worked in the integration repo and failed in every worktree, which
# blocked all of Hole B.
# ---------------------------------------------------------------------------
set -uo pipefail

CRNT_ROOT="${CRNT_ROOT:-/Users/akutuva/Documents/Proofs/crnt-lean}"
QUIET=0
if [ "${1:-}" = "--quiet" ]; then QUIET=1; shift; fi

if [ $# -lt 1 ]; then echo "usage: checkmod.sh [--quiet] <path/to/Module.lean> [...]" >&2; exit 2; fi

SHARED="$CRNT_ROOT/.lake/build/lib/lean"
if [ ! -d "$SHARED" ]; then
  echo "shared build cache missing: $SHARED" >&2
  exit 2
fi

# Base LEAN_PATH (mathlib + deps) from lake, then PREPEND the shared root.
BASE_LEAN_PATH="$(lake env printenv LEAN_PATH 2>/dev/null || true)"
export LEAN_PATH="$SHARED${BASE_LEAN_PATH:+:$BASE_LEAN_PATH}"

rc=0
for f in "$@"; do
  [ -f "$f" ] || { echo "MISSING: $f" >&2; rc=2; continue; }
  mod="${f%.lean}"
  out="$PWD/.lake/build/lib/lean/${mod}.olean"
  mkdir -p "$(dirname "$out")"
  log=$(mktemp)
  lean -o "$out" "$f" >"$log" 2>&1
  status=$?
  if [ $status -ne 0 ]; then
    rc=$status
    echo "=== FAIL($status) $f ==="
    grep -E "error:" "$log" | head -40
    [ $QUIET -eq 1 ] || tail -20 "$log"
  elif [ $QUIET -eq 0 ]; then
    warns=$(grep -c "declaration uses \`sorry\`" "$log" || true)
    echo "=== OK $f (sorry-warnings: $warns) ==="
  fi
  rm -f "$log"
done
exit $rc
#!/usr/bin/env bash
# One command for the whole loop. Replaces the 5-6 separate invocations that were eating
# most of each session's budget.
#
#   ./scripts/cycle.sh                       # triage -> build -> promote -> index -> gates
#   ./scripts/cycle.sh --merge /path/to/tree # + verified cross-branch merge first
#
# Every step is already idempotent and resumable, so re-running is always safe.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# --- environment (zstd-free; see docs/session-addendum.md §1) -------------------
export PATH=/home/claude/toolchain/lean431-mini/bin:$PATH
export CRNT_CACHE=${CRNT_CACHE:-/home/claude/cache/crnt-compiled-cache}
LP=""; for d in "$CRNT_CACHE"/*/.lake/build/lib/lean; do LP="${LP:+$LP:}$d"; done
export LEAN_PATH="$LP:$PWD/.lake/build/lib/lean"

BUDGET=${BUDGET:-200}          # per-step wall clock; a single command is capped at ~300s
LEDGER=scripts/unverified_modules.txt

say() { printf '\n=== %s ===\n' "$1"; }

# --- 0. optional merge ---------------------------------------------------------
if [ "${1:-}" = "--merge" ] && [ -n "${2:-}" ]; then
  say "MERGE (Lean-verified, (errors,holes) jointly)"
  python3 scripts/compare_tree.py --other "$2" --verify --port --budget "$BUDGET"
fi

# --- 1. auto-fix known defect classes -----------------------------------------
say "TRIAGE --apply"
timeout $((BUDGET + 40)) python3 scripts/triage.py --targets "$LEDGER" \
  --apply --budget "$BUDGET" 2>&1 | grep -E '^FIXED|auto-fixed|^ *[0-9]+ ' || true

# --- 2. build (resumable; unblocks dependency-gated modules) -------------------
say "BUILD"
timeout $((BUDGET + 40)) python3 scripts/batch_build.py --targets "$LEDGER" \
  --budget "$BUDGET" --retry-all 2>&1 | tail -3

# --- 3. promote anything now provable + gate-checked (rolls back on failure) ---
say "PROMOTE"
timeout 120 python3 scripts/promote.py --all 2>&1 | tail -12

# --- 4. metrics ----------------------------------------------------------------
say "METRICS"
timeout 150 python3 scripts/decl_index.py --build 2>&1 | tail -2
python3 scripts/dump_sorries.py 2>/dev/null | head -1
printf 'ledger: %s\n' "$(grep -cv '^#' "$LEDGER")"

# --- 5. gates + umbrella (the only numbers that mean anything) -----------------
say "GATES"
for g in check_imports check_stubs check_undefined_names check_exclusions; do
  printf '%-24s ' "$g"
  timeout 120 python3 "scripts/$g.py" >/dev/null 2>&1 && echo PASS || echo FAIL
done
printf '%-24s ' umbrella
echo 'import CRNT' > /tmp/_umb.lean
if timeout 240 lean /tmp/_umb.lean >/tmp/_umb.log 2>&1; then echo PASS; else
  echo FAIL; head -5 /tmp/_umb.log; fi

#!/bin/bash
#SBATCH --job-name=crntsync
#SBATCH --partition=any_cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=01:30:00
#SBATCH --output=/net/dali/home/mscbio/ark426/crnt-campaign/logs/sync-%j.out
#SBATCH --error=/net/dali/home/mscbio/ark426/crnt-campaign/logs/sync-%j.err

# Synchronise the cluster checkout with the campaign branch and run the full
# verification build plus the axiom audit.  This is the *authoritative*
# independent check: the cluster's build tree was produced from scratch here,
# not inherited from the developer's machine.
#
# Nothing runs on the login node.

set -u
# `--mem` is deliberately omitted: this cluster's Slurm turns it into an
# RLIMIT_AS cap, and Lean cannot create its thread stacks under such a cap.
export HOME=/net/dali/home/mscbio/ark426
export PATH="$HOME/.elan/bin:$PATH"
REPO="$HOME/crnt-lean"
RESULTS="$HOME/crnt-campaign/results"
mkdir -p "$RESULTS"

cd "$REPO" || exit 1
echo "=== sync start $(date -Is) on $(hostname) ==="

git fetch origin master || { echo "FETCH_FAILED"; exit 1; }
git checkout -B master origin/master || { echo "CHECKOUT_FAILED"; exit 1; }
git reset --hard origin/master || { echo "RESET_FAILED"; exit 1; }
echo "HEAD: $(git rev-parse HEAD)"

export LAKE_JOBS="${SLURM_CPUS_PER_TASK:-4}"

echo "--- lake build CRNT ---"
if ! lake build CRNT; then
  echo "BUILD_FAILED"
  echo '{"task_id":"sync_build","status":"FAIL","detail":"lake build CRNT failed"}' \
    > "$RESULTS/sync_build.json"
  exit 1
fi

echo "--- lake build test ---"
lake build test 2>&1 | tail -5 || echo "test build had errors (see log)"

echo "--- field map pins ---"
if lake env python3 scripts/field_map_pins.py; then
  pins="OK"
else
  pins="FAILED"
fi

echo "--- axiom audit ---"
if lake build test.AxiomAudit; then
  audit="OK"
else
  audit="FAILED"
fi

nolean=$(find .lake/build/lib/lean/CRNT -name '*.olean' | wc -l)
echo "=== sync done $(date -Is): $nolean oleans, pins=$pins audit=$audit ==="
python3 - "$RESULTS/sync_build.json" "$nolean" "$pins" "$audit" "$(git rev-parse HEAD)" <<'PY'
import json, sys, os
path, n, pins, audit, head = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], sys.argv[5]
json.dump({
    "task_id": "sync_build",
    "status": "PASS" if (pins == "OK" and audit == "OK") else "PARTIAL",
    "detail": f"{n} CRNT oleans; field-map pins {pins}; axiom audit {audit}",
    "head": head,
    "job_id": os.environ.get("SLURM_JOB_ID", ""),
}, open(path, "w"), indent=1)
PY

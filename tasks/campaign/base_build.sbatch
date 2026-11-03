#!/bin/bash
#SBATCH --job-name=crntbase
#SBATCH --partition=any_cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --time=02:00:00
#SBATCH --output=/net/dali/home/mscbio/ark426/crnt-campaign/logs/%x-%j.out
#SBATCH --error=/net/dali/home/mscbio/ark426/crnt-campaign/logs/%x-%j.err

# One-time base build of the CRNT library on the cluster.
#
#   1. fetch the prebuilt Mathlib oleans (`lake exe cache get`),
#   2. build the CRNT core (`lake build CRNT`) with all allocated cores,
#   3. record a machine-readable completion marker.
#
# Nothing here ever runs on the login node: it is a Slurm batch script.

set -u
# NOTE ON MEMORY: this cluster's Slurm applies `--mem` as an RLIMIT_AS (address-space)
# cap.  Lean reserves a large virtual arena and creates one thread stack per worker,
# so any `--mem` below ~32G makes `lake build` abort with
# "failed to create thread: Resource temporarily unavailable".  The job therefore
# requests no address-space cap; the *actual* consumption is read back from
# `sacct` (MaxRSS) by the orchestrator.
export HOME=/net/dali/home/mscbio/ark426
export PATH="$HOME/.elan/bin:$PATH"
REPO="$HOME/crnt-lean"
RESULTS="$HOME/crnt-campaign/results"
mkdir -p "$RESULTS"

cd "$REPO" || exit 1
echo "=== base build start $(date -Is) on $(hostname) ==="
nproc
git rev-parse HEAD

step() { echo "--- $* ($(date +%s)) ---"; }

echo "--- environment ---"
nproc
ulimit -u
cat /sys/fs/cgroup/pids.max 2>/dev/null || echo "no pids.max"
cat /sys/fs/cgroup/pids.current 2>/dev/null || true
export LAKE_JOBS="${SLURM_CPUS_PER_TASK:-4}"

step "lake exe cache get"
if ! lake exe cache get; then
  echo "CACHE_GET_FAILED"
  echo '{"task_id":"base_build","status":"FAIL","detail":"lake exe cache get failed"}' \
    > "$RESULTS/base_build.json"
  exit 1
fi

step "lake build CRNT"
if ! lake build CRNT; then
  echo "BUILD_FAILED"
  echo '{"task_id":"base_build","status":"FAIL","detail":"lake build CRNT failed"}' \
    > "$RESULTS/base_build.json"
  exit 1
fi

step "lake build CRNTFrontier"
lake build CRNTFrontier || echo "frontier build failed (expected)"

nmodules=$(find .lake/build/lib/lean/CRNT -name '*.olean' 2>/dev/null | wc -l)
echo "=== base build done $(date -Is); $nmodules CRNT oleans ==="
python3 - "$RESULTS/base_build.json" "$nmodules" <<'PY'
import json, sys, os
path, n = sys.argv[1], int(sys.argv[2])
json.dump({
    "task_id": "base_build",
    "status": "PASS",
    "detail": f"{n} CRNT oleans built",
    "job_id": os.environ.get("SLURM_JOB_ID", ""),
    "elapsed_s": os.environ.get("SLURM_JOB_ELAPSED", ""),
}, open(path, "w"), indent=1)
PY
exit 0

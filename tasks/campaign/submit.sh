#!/bin/bash
# Submit a CRNT verification job to the any_cpu partition.
#
#   submit.sh <task_id> <module-path> <commit> [extra_src ...]
#
# Environment for the job:
#   TASK_ID, MODULE, COMMIT, EXTRA_SRC, WORKDIR
#
# The job runs on a compute node only; the login node is never used for
# compilation.
set -eu
export HOME=/net/dali/home/mscbio/ark426
export PATH=/opt/slurm/bin:$PATH

TASK_ID="$1"; shift
MODULE="$1"; shift
COMMIT="$1"; shift

RESULTS="$HOME/crnt-campaign/results"
mkdir -p "$RESULTS" "$HOME/crnt-campaign/logs"

# How many campaign jobs are already running or pending?
running=$(squeue -h -u "$USER" -o "%j" 2>/dev/null | grep -c '^crntv' || true)
pending=$(squeue -h -u "$USER" -t PD -o "%j" 2>/dev/null | grep -c '^crntv' || true)
echo "campaign verification jobs: running=$running pending=$pending"

extra=""
for spec in "$@"; do
  extra="$extra ${spec}"
done

jobid=$(TASK_ID="$TASK_ID" MODULE="$MODULE" COMMIT="$COMMIT" EXTRA_SRC="$extra" \
  WORKDIR="/scr/crnt/$TASK_ID" \
  sbatch --parsable \
    --job-name="crntv" \
    --partition=any_cpu --nodes=1 --ntasks=1 --cpus-per-task=2 --mem=8G \
    --time=00:45:00 \
    --output="$HOME/crnt-campaign/logs/crntv-%j.out" \
    --error="$HOME/crnt-campaign/logs/crntv-%j.err" \
    "$HOME/crnt-campaign/verify_module.sbatch")
echo "$jobid" > "$RESULTS/$TASK_ID.jobid"
echo "submitted $TASK_ID ($MODULE @ $COMMIT) as job $jobid"

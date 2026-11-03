#!/bin/bash
#SBATCH --job-name=crntv
#SBATCH --partition=any_cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=00:45:00
#SBATCH --output=/net/dali/home/mscbio/ark426/crnt-campaign/logs/%x-%j.out
#SBATCH --error=/net/dali/home/mscbio/ark426/crnt-campaign/logs/%x-%j.err

# Verify one CRNT module in isolation.
#
# Environment (set by the submitter):
#   TASK_ID     unique task identifier
#   MODULE      repo-relative module path, e.g. CRNT/Multistationarity/Foo.lean
#   COMMIT      git commit the sources were taken from
#   WORKDIR     scratch dir for this job
#   REPO        canonical checkout on the cluster
#   EXTRA_SRC   optional "dest=src" list of files to overlay into the worktree
#
# The job never mutates the canonical build directory: it compiles the module
# into a private scratch olean using the shared (read-only) LEAN_PATH.

set -u
REPO="${REPO:-$HOME/crnt-lean}"
TASK_ID="${TASK_ID:-unknown}"
MODULE="${MODULE:?MODULE must be set}"
COMMIT="${COMMIT:-unknown}"
WORKDIR="${WORKDIR:-/scr/crnt/$TASK_ID}"
export PATH="$HOME/.elan/bin:$PATH"

mkdir -p "$WORKDIR"
WT="$WORKDIR/wt"
RESULTS="$HOME/crnt-campaign/results"
mkdir -p "$RESULTS"

status="FAIL"
detail=""
axioms_out="$WORKDIR/axioms.txt"

finish() {
  python3 - "$RESULTS/$TASK_ID.json" "$TASK_ID" "$MODULE" "$COMMIT" "$status" "$detail" <<'PY'
import json, sys, os
path, tid, module, commit, status, detail = sys.argv[1:7]
rec = {
    "task_id": tid,
    "module": module,
    "commit": commit,
    "status": status,
    "detail": detail[:4000],
    "job_id": os.environ.get("SLURM_JOB_ID", ""),
    "cpus": os.environ.get("SLURM_CPUS_PER_TASK", ""),
    "mem": os.environ.get("SLURM_MEM_PER_NODE", ""),
    "elapsed_s": os.environ.get("SLURM_JOB_ELAPSED", ""),
}
with open(path, "w") as fh:
    json.dump(rec, fh, indent=1)
PY
}
trap finish EXIT

cd "$REPO" || { detail="no repo"; exit 1; }

# 1. materialise an isolated worktree at the recorded commit
rm -rf "$WT"
if git worktree add --detach "$WT" "$COMMIT" >"$WORKDIR/worktree.log" 2>&1; then
  :
else
  # commit may be a local-only commit; fall back to the working tree copy
  mkdir -p "$WT"
  git archive "$COMMIT" 2>/dev/null | tar -x -C "$WT" || cp -a "$REPO/." "$WT/"
fi

# 2. share the dependency packages read-only
mkdir -p "$WT/.lake"
if [ ! -e "$WT/.lake/packages" ]; then
  ln -s "$REPO/.lake/packages" "$WT/.lake/packages" 2>/dev/null || true
fi

# 3. overlay any extra sources the orchestrator wants verified
if [ -n "${EXTRA_SRC:-}" ]; then
  for pair in $EXTRA_SRC; do
    dst="${pair%%=*}"; src="${pair#*=}"
    mkdir -p "$WT/$(dirname "$dst")"
    cp -f "$src" "$WT/$dst"
  done
fi

# 4. the shared LEAN_PATH (mathlib + the built CRNT core)
LEAN_PATH_EXPORT="$WORKDIR/leanpath.txt"
( cd "$REPO" && lake env printenv LEAN_PATH ) > "$LEAN_PATH_EXPORT" 2>/dev/null
if [ ! -s "$LEAN_PATH_EXPORT" ]; then
  detail="could not export LEAN_PATH"
  exit 1
fi
export LEAN_PATH="$(cat "$LEAN_PATH_EXPORT")"

modname="${MODULE%.lean}"
modname="${modname//\//.}"

# 5. compile the module in isolation
mkdir -p "$WORKDIR/out"
if ! ( cd "$WT" && lean -o "$WORKDIR/out/module.olean" "$MODULE" ) >"$WORKDIR/build.log" 2>&1; then
  detail="compile failed: $(tail -c 2500 "$WORKDIR/build.log")"
  exit 1
fi

# 6. axiom audit: every declaration of the module must be free of sorryAx
cat > "$WORKDIR/audit.lean" <<EOF
import $modname
EOF
grep -oE '^(theorem|lemma|def|noncomputable def|example|abbrev|structure|class|inductive|instance) +[^ :(]*' \
  "$WT/$MODULE" | awk '{print $NF}' | sed 's/:$//' | sort -u | while read -r d; do
  [ -z "$d" ] && continue
  printf '#print axioms %s\n' "$d" >> "$WORKDIR/audit.lean"
done
if ! ( cd "$WT" && lean "$WORKDIR/audit.lean" ) >"$axioms_out" 2>&1; then
  detail="audit failed: $(tail -c 1500 "$axioms_out")"
  exit 1
fi
if grep -q "sorryAx" "$axioms_out"; then
  detail="sorryAx present: $(grep -B1 sorryAx "$axioms_out" | head -20)"
  exit 1
fi
if grep -qE "^\s*'[^']*' depends on axioms: \[.*\]" "$axioms_out"; then
  # informational only; the allowed set is checked by the orchestrator
  :
fi
nax=$(grep -c "depends on axioms" "$axioms_out")
detail="compiled ok; audited $nax declaration(s)"
status="PASS"
exit 0

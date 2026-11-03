#!/bin/bash
#SBATCH --job-name=crntdiag
#SBATCH --partition=any_cpu
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --time=00:10:00
#SBATCH --output=/net/dali/home/mscbio/ark426/crnt-campaign/logs/diag-%j.out
#SBATCH --error=/net/dali/home/mscbio/ark426/crnt-campaign/logs/diag-%j.err

# Diagnose why `lake build` cannot create threads inside a Slurm allocation.

set -u
export HOME=/net/dali/home/mscbio/ark426
export PATH="$HOME/.elan/bin:$PATH"

echo "=== hostname / date ==="
hostname; date
echo "=== nproc ==="; nproc
echo "=== ulimit -a ==="; ulimit -a
echo "=== cgroup ==="
cat /proc/self/cgroup
for f in $(find /sys/fs/cgroup -maxdepth 3 -name pids.max 2>/dev/null | head -10); do
  echo "--- $f ---"; cat "$f" 2>/dev/null
done
for f in $(find /sys/fs/cgroup -maxdepth 3 -name pids.current 2>/dev/null | head -10); do
  echo "--- $f ---"; cat "$f" 2>/dev/null
done
echo "=== memory ==="
free -m
echo "=== /dev/shm ==="; df -h /dev/shm 2>/dev/null
echo "=== thread creation test ==="
python3 - <<'PY'
import os, resource
soft, hard = resource.getrlimit(resource.RLIMIT_NPROC)
print("RLIMIT_NPROC", soft, hard)
for n in (32, 64, 128, 256, 512, 1024):
    try:
        import threading
        ts = [threading.Thread(target=lambda: None) for _ in range(n)]
        for t in ts: t.start()
        for t in ts: t.join()
        print("threads ok:", n)
        break
    except Exception as e:
        print("threads failed at", n, ":", e)
        break
PY
echo "=== lean thread test ==="
cd ~/crnt-lean
cat > /tmp/thr.lean <<'EOF'
import Lean
#eval show IO Unit from do
  let mut ts : Array (IO Unit) := #[]
  for i in [:200] do
    ts := ts.push (IO.asTask (prio := .dedicated) (m := 1) (fun _ => pure ()))
  for t in ts do
    match t with
    | .ok _ => pure ()
    | .error e => pure ()
  IO.println "lean threads ok"
EOF
timeout 120 lean --run /tmp/thr.lean 2>&1 | tail -5
echo "=== done ==="

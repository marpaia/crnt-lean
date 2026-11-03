#!/bin/bash
# Watcher: wait for the Lean toolchain to finish installing, then stop the
# chained `lake exe cache get` step so that no Lean compilation ever happens
# on the login node.  The cache fetch + build are resubmitted to Slurm.
export HOME=/net/dali/home/mscbio/ark426
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.34.0"
for i in $(seq 1 720); do
  if [ -x "$TC/bin/lean" ]; then
    # toolchain present: kill the parent chain that would run `lake exe cache get`
    pkill -f "elan toolchain install leanprover/lean4:v4.34.0" 2>/dev/null
    sleep 1
    pkill -f "lake exe cache get" 2>/dev/null
    echo "toolchain ready at $(date)"
    exit 0
  fi
  sleep 5
done
echo "timeout waiting for toolchain"
exit 1

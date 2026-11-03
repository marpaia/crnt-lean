#!/usr/bin/env bash
# Orchestrator-side integration of a batch of verified worker modules.
#
#   integrate.sh <module-path> [<module-path> ...]
#
# Steps (orchestrator only — workers never run this):
#   1. sanity-check the module exists and contains no sorry/admit/axiom,
#   2. add its `import` to CRNT.lean (idempotent, in the import block),
#   3. re-elaborate the module and its new dependents,
#   4. regenerate the field-map audit and run the static gates,
#   5. report the diff for review.
#
# It does NOT commit; the orchestrator reviews and commits.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

if [ $# -eq 0 ]; then
  echo "usage: $0 <module-path> ..." >&2
  exit 2
fi

for mod in "$@"; do
  if [ ! -f "$mod" ]; then
    echo "missing module: $mod" >&2
    exit 1
  fi
done
python3 tasks/campaign/check_module.py "$@" || exit 1

for mod in "$@"; do
  modname="${mod%.lean}"
  modname="${modname//\//.}"
  imp="import $modname"
  if ! grep -qxF "$imp" CRNT.lean; then
    python3 - "$imp" <<'PY'
import sys
imp = sys.argv[1]
path = "CRNT.lean"
lines = open(path).read().split("\n")
last = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines.insert(last + 1, imp)
open(path, "w").write("\n".join(lines))
print("added:", imp)
PY
  fi
done

echo "=== re-elaborating ==="
lake build +CRNT

echo "=== static gates ==="
python3 scripts/check_exclusions.py
python3 scripts/check_imports.py
python3 scripts/check_stubs.py

echo "=== field-map pins ==="
lake env python3 scripts/field_map_pins.py

echo "=== git status ==="
git status --short

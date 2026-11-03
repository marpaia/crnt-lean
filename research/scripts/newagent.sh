#!/usr/bin/env bash
# newagent.sh — provision a researcher: branch + worktree + shared package symlink.
#
#   research/scripts/newagent.sh form-panels
#
# Idempotent.  Safe to re-run for an existing agent (it just re-points the worktree).
set -euo pipefail

NAME="${1:?usage: newagent.sh <agent-name>}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
WTROOT="${CRNT_WT_ROOT:-$(dirname "$ROOT")/crnt-wt}"
BRANCH="research/$NAME"
WT="$WTROOT/$NAME"

mkdir -p "$WTROOT"

if [ ! -d "$WT" ]; then
  git -C "$ROOT" fetch origin --quiet 2>/dev/null || true
  if git -C "$ROOT" show-ref --verify --quiet "refs/heads/$BRANCH"; then
    git -C "$ROOT" worktree add "$WT" "$BRANCH"
  else
    git -C "$ROOT" worktree add -b "$BRANCH" "$WT" research/swarm
  fi
fi

# Shared Mathlib/dependency cache: symlinked, never copied.
mkdir -p "$WT/.lake"
if [ ! -e "$WT/.lake/packages" ]; then
  ln -s "$ROOT/.lake/packages" "$WT/.lake/packages"
fi

mkdir -p "$WT/research/routes" "$WT/research/papers"

cat <<EOF
agent:    $NAME
branch:   $BRANCH
worktree: $WT

cd "$WT"
export CRNT_ROOT="$ROOT"
research/scripts/checkmod.sh CRNT/Path/To/Module.lean
git commit -am "..." && git push -f origin $BRANCH
EOF
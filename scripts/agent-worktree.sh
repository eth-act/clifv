#!/usr/bin/env bash
# Create an isolated git worktree for an agent: branch agent/<name> off main, at
# <primary-checkout>/.worktrees/<name>, with pinned
# third_party sources symlinked. Build caches are not copied automatically.
# Prints the worktree path.
#
# usage: scripts/agent-worktree.sh <name> [base-ref]
set -euo pipefail
name=$1; base=${2:-main}
checkout=$(cd "$(dirname "$0")/.." && pwd)
# Always use the primary checkout, even when invoked from a linked worktree.
common=$(git -C "$checkout" rev-parse --path-format=absolute --git-common-dir)
root=$(cd "$common/.." && pwd)
wt=$root/.worktrees/$name
# Leave room for other projects and subsequent builds on the shared filesystem.
# A fresh worktree must not silently duplicate a large warm build cache.
if [ ! -d "$wt" ]; then
  available_kib=$(df -Pk "$root" | awk 'END {print $4}')
  if [ "$available_kib" -lt 104857600 ]; then
    echo "Need at least 100 GiB free before creating a worktree; clean unneeded project outputs first." >&2
    exit 1
  fi
fi
mkdir -p "$root/.worktrees"
# Idempotent: an existing branch agent/<name> is reused, an existing worktree is completed
# (missing third_party links are added), so a half-created worktree never remains.
if [ ! -d "$wt" ]; then
  if git -C "$root" show-ref --verify --quiet "refs/heads/agent/$name"; then
    git -C "$root" worktree add -q "$wt" "agent/$name"
  else
    git -C "$root" worktree add -q -b "agent/$name" "$wt" "$base"
  fi
fi
[ -e "$wt/third_party/wasmtime" ] || ln -s "$root/third_party/wasmtime" "$wt/third_party/wasmtime"
[ -e "$wt/third_party/lnsym-upstream" ] || ln -s "$root/third_party/lnsym-upstream" "$wt/third_party/lnsym-upstream"
echo "$wt"

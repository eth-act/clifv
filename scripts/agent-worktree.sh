#!/usr/bin/env bash
# Create an isolated git worktree for an agent: branch agent/<name> off main, at
# <primary-checkout>/.worktrees/<name>, with warm build caches copied from the integrator checkout and the pinned
# third_party sources symlinked. Prints the worktree path.
#
# usage: scripts/agent-worktree.sh <name> [base-ref]
set -euo pipefail
name=$1; base=${2:-main}
checkout=$(cd "$(dirname "$0")/.." && pwd)
# Always use the primary checkout, even when invoked from a linked worktree.
common=$(git -C "$checkout" rev-parse --path-format=absolute --git-common-dir)
root=$(cd "$common/.." && pwd)
wt=$root/.worktrees/$name
mkdir -p "$root/.worktrees"
# Idempotent: an existing branch agent/<name> is reused, an existing worktree is completed
# (missing third_party links and caches are added), so a half-created worktree never remains.
if [ ! -d "$wt" ]; then
  if git -C "$root" show-ref --verify --quiet "refs/heads/agent/$name"; then
    git -C "$root" worktree add -q "$wt" "agent/$name"
  else
    git -C "$root" worktree add -q -b "agent/$name" "$wt" "$base"
  fi
fi
[ -e "$wt/third_party/wasmtime" ] || ln -s "$root/third_party/wasmtime" "$wt/third_party/wasmtime"
[ -e "$wt/third_party/lnsym-upstream" ] || ln -s "$root/third_party/lnsym-upstream" "$wt/third_party/lnsym-upstream"
if [ -d "$root/.lake" ] && [ ! -d "$wt/.lake" ]; then cp -a "$root/.lake" "$wt/.lake"; fi
if [ -d "$root/rust/target" ] && [ ! -d "$wt/rust/target" ]; then cp -a "$root/rust/target" "$wt/rust/target"; fi
echo "$wt"

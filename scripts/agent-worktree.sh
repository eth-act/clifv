#!/usr/bin/env bash
# Create an isolated git worktree for an agent: branch agent/<name> off main, at
# ../clifv-wt/<name>, with warm build caches copied from the integrator checkout and the pinned
# third_party sources symlinked. Prints the worktree path.
#
# usage: scripts/agent-worktree.sh <name> [base-ref]
set -euo pipefail
name=$1; base=${2:-main}
root=$(cd "$(dirname "$0")/.." && pwd)
wt=$(dirname "$root")/clifv-wt/$name
git -C "$root" worktree add -q -b "agent/$name" "$wt" "$base"
ln -s "$root/third_party/wasmtime" "$wt/third_party/wasmtime"
ln -s "$root/third_party/lnsym-upstream" "$wt/third_party/lnsym-upstream"
[ -d "$root/.lake" ] && cp -a "$root/.lake" "$wt/.lake"
[ -d "$root/rust/target" ] && cp -a "$root/rust/target" "$wt/rust/target"
echo "$wt"

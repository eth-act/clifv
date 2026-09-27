#!/usr/bin/env bash
# Snapshot the entire working tree (tracked + untracked, respecting .gitignore) as a commit
# on branch `wip`, and push it. Does not touch HEAD, the real index, or any working-tree file,
# so it is safe to run while agents are editing.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp_index=$(mktemp)
trap 'rm -f "$tmp_index"' EXIT
export GIT_INDEX_FILE="$tmp_index"
git read-tree HEAD
git add -A .
tree=$(git write-tree)
parent=$(git rev-parse -q --verify refs/heads/wip || git rev-parse HEAD)
if [ "$(git rev-parse "$parent^{tree}")" = "$tree" ]; then
  echo "wip: no changes"; exit 0
fi
head=$(git rev-parse HEAD)
parents=(-p "$parent")
[ "$parent" != "$head" ] && parents+=(-p "$head")
commit=$(git commit-tree "$tree" "${parents[@]}" -m "WIP snapshot $(date -u +%FT%TZ) (base $(git rev-parse --short HEAD))")
git update-ref refs/heads/wip "$commit"
git push -q -f origin wip
echo "wip: $commit pushed"

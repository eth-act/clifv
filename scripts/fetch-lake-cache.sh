#!/usr/bin/env bash
# Fill the shared Lake cache ($FV_LAKE_CACHE, docs/TO-PROVE.md §7) with CI's build of main, so a
# local `lake build` or scripts/lake-serial-build.py rebuilds only what differs from it.
#
# usage: scripts/fetch-lake-cache.sh [REF]      (default HEAD; needs gh with read access)
#
# Picks the `lake-full` artifact of the full gate (.github/workflows/full-gate.yml) from the newest
# main commit that REF contains, else the newest one. A partial build (some modules failed) is
# fine: Lake builds whatever the cache lacks. Needs about twice the artifact's size (~7 GB) in
# $TMPDIR while it unpacks.
set -euo pipefail
cd "$(dirname "$0")/.."
ref=${1:-HEAD}
cache=${FV_LAKE_CACHE:-${LAKE_CACHE_DIR:-}}
[[ -n $cache ]] || { echo "set FV_LAKE_CACHE to the shared cache directory (docs/USAGE.md)" >&2; exit 2; }
repo=${FV_REPO:-eth-act/clifv}
pick=
while read -r id sha created; do
  if git cat-file -e "$sha^{commit}" 2>/dev/null && git merge-base --is-ancestor "$sha" "$ref"; then
    pick="$id $sha $created"; break
  fi
  [[ -n ${first:-} ]] || first="$id $sha $created"
done < <(gh api "repos/$repo/actions/artifacts?name=lake-full&per_page=100" --jq '
  [.artifacts[] | select((.expired | not) and .workflow_run.head_branch == "main")]
  | sort_by(.created_at) | reverse | .[] | "\(.id) \(.workflow_run.head_sha) \(.created_at)"')
if [[ -z $pick ]]; then
  [[ -n ${first:-} ]] || { echo "no unexpired lake-full artifact on main" >&2; exit 1; }
  pick=$first
  echo "no lake-full of a commit that $ref contains; using the newest one" >&2
fi
read -r id sha created <<< "$pick"
echo "lake-full artifact $id: main ${sha:0:8}, built $created"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
gh api "repos/$repo/actions/artifacts/$id/zip" > "$tmp/a.zip"
python3 -m zipfile -e "$tmp/a.zip" "$tmp/x"
rm "$tmp/a.zip"
mkdir -p "$cache"
LAKE_CACHE_DIR=$cache python3 scripts/lake-unstage.py "$tmp/x"
echo "cache $cache: $(du -sh "$cache" | cut -f1)"

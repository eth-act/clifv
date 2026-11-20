#!/usr/bin/env bash
# BaselineD1: midval-check --cert over every dump directory of every crate (MidendNorm2 run-check.sh, dumps dir as argument).
#   run-check.sh DUMPS OUTDIR [flags...]   env X = checker binary
set -uo pipefail
B=$1 O=$2; shift 2
export FL="--cert $*"
mkdir -p "$O"
t0=$(date +%s)
for d in "$B"/*/; do
  c=$(basename "$d")
  find "$d" -mindepth 1 -maxdepth 1 -type d | sort | xargs -P "${P:-16}" -I{} sh -c "\"\$X\" \$FL \"\$1\" >\"\$1.v.tsv\"" _ {}
  cat "$d"/*.v.tsv >"$O/$c.tsv"
  rm -f "$d"/*.v.tsv
  echo "$c $(wc -l <"$O/$c.tsv") pairs, $(grep -c "	accept	" "$O/$c.tsv") accepted, $(cut -f8 "$O/$c.tsv" | grep -c "^ok$") recheck ok, $(cut -f8 "$O/$c.tsv" | grep -c MISMATCH) mismatch"
done
echo "wall $(( $(date +%s) - t0 ))s"

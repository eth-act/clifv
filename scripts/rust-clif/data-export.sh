#!/usr/bin/env bash
# Write cg_clif's data objects for every dumped crate of the survey corpus (clif-data-export).
#   scripts/rust-clif/data-export.sh [OUT_DIR]      (default ${TMPDIR:-/tmp}/rust-clif-survey/out)
# Writes OUT/../data/<profile>-<crate>.data.clif and a summary line per run.
set -uo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:-${TMPDIR:-/tmp}/rust-clif-survey/out}
tool="$root/rust/target/release/clif-data-export"
data="$out/../data"
mkdir -p "$data"
fail=0
for prof in debug release release-oc; do
  for d in "$out/$prof"/*; do
    c=$(basename "$d")
    [[ -f "$d/$c.o" ]] || continue
    line=$("$tool" "$d/$c.o" --out "$data/$prof-$c.data.clif") || fail=1
    if [[ $fail -eq 1 ]]; then echo "FAIL $prof/$c"; exit 1; fi
    echo "$prof $c $line"
  done
done | awk '{gsub(/[,}]/, ""); o+=$6; b+=$8; u+=$10; print} END {printf "TOTAL objects=%d bytes=%d unsupported=%d\n", o, b, u; exit '"$fail"'}'

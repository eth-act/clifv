#!/usr/bin/env bash
# Recover cg_clif's data objects for every dumped crate of the survey corpus.
#   scripts/rust-clif/data-export.sh [OUT_DIR]      (default /tmp/rust-clif-survey/out)
# Writes OUT/../data/<profile>-<crate>.{data.clif,gvmap.tsv} and a summary line per run.
set -uo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=${1:-/tmp/rust-clif-survey/out}
tool="$root/rust/target/release/clif-data-export"
data="$out/../data"
mkdir -p "$data"
fail=0
total_fns=0; total_wd=0; total_obj=0; total_bytes=0
for prof in debug release release-oc; do
  for d in "$out/$prof"/*; do
    c=$(basename "$d")
    [[ -f "$d/$c.o" ]] || continue
    line=$("$tool" "$d/$c.clif" "$d/$c.o" --out "$data/$prof-$c.data.clif" --gvmap "$data/$prof-$c.gvmap.tsv") || fail=1
    if [[ $fail -eq 1 ]]; then echo "FAIL $prof/$c"; exit 1; fi
    echo "$prof $c $line"
  done
done | awk '{f+=$6; wd+=$8; o+=$10; b+=$12; print} END {printf "TOTAL fns=%d with_data=%d objects=%d bytes=%d\n", f, wd, o, b; exit '"$fail"'}'

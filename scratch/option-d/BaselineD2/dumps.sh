#!/usr/bin/env bash
# BaselineD2 (option D measurement, scratch): regenerate cg_clif's (unopt, opt) dump pairs of the
# release crates whose dumps release.sh did not save (num-traits, blake2, sha3, itoa), with the
# SAME source path, cargo-fv and cg_clif path (target/cg_clif-active) as BaselineD1's release.sh,
# so symbol names match rel-<cl>/<crate>/parity-*.json. No Lean compilation (FV_ONLY matches
# nothing, as MidendNorm1's gen-dumps.sh): cg_clif writes <unit>.clif/ directories.
#   dumps.sh <crate> <version>...   (pairs)  -> ~/clifv/tmp/BaselineD1/dumps-<cl>/<crate>-<ver>/<n>/
set -uo pipefail
S=$HOME/clifv/tmp/CrateSurvey2
B=$HOME/clifv/tmp/BaselineD1
W=${W:-$HOME/clifv/wt/BaselineD1-meas}
act=$W/target/cg_clif-active
export FV_JOBS=${RS_JOBS:-8} CARGO_BUILD_JOBS=${RS_JOBS:-8}
export CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=fallback
export CC_aarch64_unknown_linux_musl=aarch64-linux-gnu-gcc AR_aarch64_unknown_linux_musl=aarch64-linux-gnu-ar
while [ $# -ge 2 ]; do
  c=$1 v=$2; shift 2
  for cl in ${CLS:-0.135.0 0.136.1}; do
    dd=cg_clif; [[ $cl == 0.136.1 ]] && dd=cg_clif-cl0.136.1
    rm -rf "$act" && mkdir -p "$act" && cp -r "$W/target/$dd/unwind" "$W/target/$dd/abort" "$act/"
    d=$B/src/$c-$v
    D=$B/dumps-$cl/$c-$v
    rm -rf "$d" "$D"; mkdir -p "$D" "$B/src"
    rsync -a --exclude target "$S/src/$c-$v/" "$d/"
    cp "$S/locks/$c-$v.lock" "$d/Cargo.lock"
    SEL=--workspace TARGS=""
    [ -f "$S/extra/$c-$v.env" ] && . "$S/extra/$c-$v.env"
    t0=$(date +%s)
    (cd "$d" && env FV_ONLY=__midval_no_function__ FV_ROOT="$W" PATH="$W/rust/target/release:$PATH" \
      FV_CG_CLIF="$act/unwind/librustc_codegen_cranelift.so" CARGO_TARGET_DIR="$d/target/fv" \
      cargo fv test --release $SEL --no-run >"$D/build.log" 2>&1)
    rc=$?
    n=0
    while IFS= read -r dir; do
      n=$((n + 1)); mkdir -p "$D/$n"; cp -r "$dir"/. "$D/$n/"; echo "$n $dir" >>"$D/units.txt"
    done < <(find "$d/target/fv" -type d -name '*.clif' | sort)
    echo "$c-$v $cl dumps rc=$rc wall=$(( $(date +%s) - t0 ))s units=$n unopt=$(find "$D" -name '*.unopt.clif' | wc -l) opt=$(find "$D" -name '*.opt.clif' | wc -l)"
    python3 "$B/notrap-dead.py" --json "$B/rel-$cl/$c-$v/notrap-unopt.json" "$D" | sed 's/^/  notrap unopt: /'
    python3 "$B/notrap-dead.py" --json "$B/rel-$cl/$c-$v/notrap-opt.json" --suffix .opt.clif "$D" | sed 's/^/  notrap opt: /'
    rm -rf "$d"
  done
done
rm -rf "$act"

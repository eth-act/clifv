#!/usr/bin/env bash
# BaselineD3: BaselineD2's relp.sh plus the stock-crate-parity.py call it lacked (relp.sh printed
# parity-<p>.txt but never wrote it, then deleted the target: no parity was recorded).
# BaselineD2 (option D measurement, scratch): one release crate with cg_clif on Cranelift 0.136.1
# and the PROTOTYPE drop of unused notrap loads (lean-backend of ~/clifv/wt/BaselineD1, branch
# agent/BaselineD1 79f2b9f89; FV_ROOT selects it), cargo-fv of BaselineD1-meas (FV_SCRATCH_CLIF=opt
# support), same source path and cg_clif path as release.sh (symbol names match the dumps):
#   fv     unopt input (today's route + the drop)          -> relp-0.136.1/<crate>/parity-fv.json
#   optfv  FV_SCRATCH_CLIF=opt (opt input + the drop)       -> relp-0.136.1/<crate>/parity-optfv.json
#   relp.sh <crate> <version>...
set -uo pipefail
S=$HOME/clifv/tmp/CrateSurvey2
B=$HOME/clifv/tmp/BaselineD1
B2=$HOME/clifv/tmp/BaselineD2
W=$HOME/clifv/wt/BaselineD1-meas
P=$HOME/clifv/wt/BaselineD1
act=$W/target/cg_clif-active
export FV_JOBS=${RS_JOBS:-8} CARGO_BUILD_JOBS=${RS_JOBS:-8}
export CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=fallback
export CC_aarch64_unknown_linux_musl=aarch64-linux-gnu-gcc AR_aarch64_unknown_linux_musl=aarch64-linux-gnu-ar
CAP=${CAP:-20G}
cl=0.136.1
rm -rf "$act" && mkdir -p "$act" && cp -r "$W/target/cg_clif-cl0.136.1/unwind" "$W/target/cg_clif-cl0.136.1/abort" "$act/"
while [ $# -ge 2 ]; do
  c=$1 v=$2; shift 2
  d=$B/src/$c-$v
  O=$B2/relp-$cl/$c-$v
  rm -rf "$O" "$d"; mkdir -p "$O" "$B/src"
  rsync -a --exclude target "$S/src/$c-$v/" "$d/"
  cp "$S/locks/$c-$v.lock" "$d/Cargo.lock"
  SEL=--workspace TARGS=""
  [ -f "$S/extra/$c-$v.env" ] && . "$S/extra/$c-$v.env"
  for p in ${PS:-optfv fv}; do
    sc=(); [[ $p == optfv ]] && sc=(FV_SCRATCH_CLIF=opt)
    t0=$(date +%s)
    (cd "$d" && FV_MEMCAP=$CAP "$W/scripts/memcap.sh" env FV_ROOT="$P" PATH="$W/rust/target/release:$PATH" \
      FV_CG_CLIF="$act/unwind/librustc_codegen_cranelift.so" "${sc[@]}" CARGO_TARGET_DIR="$d/target/$p" \
      cargo fv test --release $SEL --keep-temps --no-binary-check --no-run >"$O/$p.log" 2>&1)
    rc=$?
    cp "$d/target/$p/fv-report.json" "$O/$p-report.json" 2>/dev/null
    tmp=$(ls -d "$d"/target/$p/fv/*/tmp 2>/dev/null | head -1)
    FV_MEMCAP=8G "$W/scripts/memcap.sh" python3 "$W/scripts/stock-crate-parity.py" --json "$O/parity-$p.json" "$tmp" >"$O/parity-$p.txt" 2>&1
    nd=$(grep -o "unused notrap loads dropped" "$O/$p-report.json" 2>/dev/null | wc -l)
    echo "$c-$v $cl+drop $p rc=$rc wall=$(( $(date +%s) - t0 ))s $(grep -m1 -E '^cargo fv: [0-9]+ of' "$O/$p.log") | parity: $(head -1 "$O/parity-$p.txt") | functions changed by the drop: $nd"
    rm -rf "$d/target/$p"
  done
  rm -rf "$d"
done
rm -rf "$act"

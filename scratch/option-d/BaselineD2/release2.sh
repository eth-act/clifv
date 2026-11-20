#!/usr/bin/env bash
# BaselineD2: BaselineD1's release.sh with --no-binary-check (link-check on one serde_json test
# executable ran 1.5 h on one core; the binary check does not change the per-unit objects that
# stock-crate-parity.py compares). Otherwise identical (paths, cg_clif-active, outputs).
# BaselineD1 (option D measurement, scratch): one crate of the release report (#1119), release
# profile, the crate survey's sources/lockfiles/settings, with cg_clif on Cranelift 0.135.0 and
# on 0.136.1 (both copied to $W/target/cg_clif-active, so symbol names agree):
#   unopt  `cargo fv test --release --keep-temps --no-run` (main's cargo fv: Lean compiles the
#          .unopt.clif) -> parity-fv.json, and the cg_clif dump pairs (midval input)
#   opt    the same with FV_SCRATCH_CLIF=opt (scratch cargo fv: Lean compiles cg_clif's .opt.clif)
#          -> parity-optfv.json
#   release.sh <crate> <version>  -> $B/rel-<cl>/<crate>-<ver>/, dumps in $B/dumps-<cl>/<crate>-<ver>/
set -uo pipefail
c=$1 v=$2
S=$HOME/clifv/tmp/CrateSurvey2
B=$HOME/clifv/tmp/BaselineD1
W=${W:-$HOME/clifv/wt/BaselineD1-meas}
act=$W/target/cg_clif-active
export FV_JOBS=${RS_JOBS:-8} CARGO_BUILD_JOBS=${RS_JOBS:-8}
export CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=fallback
export CC_aarch64_unknown_linux_musl=aarch64-linux-gnu-gcc AR_aarch64_unknown_linux_musl=aarch64-linux-gnu-ar
CAP=${CAP:-20G}
for cl in ${CLS:-0.135.0 0.136.1}; do
  dd=cg_clif; [[ $cl == 0.136.1 ]] && dd=cg_clif-cl0.136.1
  rm -rf "$act" && mkdir -p "$act" && cp -r "$W/target/$dd/unwind" "$W/target/$dd/abort" "$act/"
  d=$B/src/$c-$v
  O=$B/rel-$cl/$c-$v
  D=$B/dumps-$cl/$c-$v
  rm -rf "$O" "$d" "$D"; mkdir -p "$O" "$D" "$B/src"
  rsync -a --exclude target "$S/src/$c-$v/" "$d/"
  cp "$S/locks/$c-$v.lock" "$d/Cargo.lock"
  SEL=--workspace TARGS=""
  [ -f "$S/extra/$c-$v.env" ] && . "$S/extra/$c-$v.env"
  for p in fv optfv; do
    sc=(); [[ $p == optfv ]] && sc=(FV_SCRATCH_CLIF=opt)
    t0=$(date +%s)
    (cd "$d" && FV_MEMCAP=$CAP "$W/scripts/memcap.sh" env FV_ROOT="$W" PATH="$W/rust/target/release:$PATH" \
      FV_CG_CLIF="$act/unwind/librustc_codegen_cranelift.so" "${sc[@]}" CARGO_TARGET_DIR="$d/target/$p" \
      cargo fv test --release $SEL --keep-temps --no-binary-check --no-run >"$O/$p.log" 2>&1)
    rc=$?
    cp "$d/target/$p/fv-report.json" "$O/$p-report.json" 2>/dev/null
    tmp=$(ls -d "$d"/target/$p/fv/*/tmp 2>/dev/null | head -1)
    FV_MEMCAP=8G "$W/scripts/memcap.sh" python3 "$W/scripts/stock-crate-parity.py" --json "$O/parity-$p.json" "$tmp" >"$O/parity-$p.txt" 2>&1
    echo "$c-$v $cl $p rc=$rc wall=$(( $(date +%s) - t0 ))s $(grep -m1 -E '^cargo fv: [0-9]+ of' "$O/$p.log") | parity: $(head -1 "$O/parity-$p.txt")"
    if [[ $p == fv ]]; then
      n=0
      while IFS= read -r dir; do
        n=$((n + 1)); mkdir -p "$D/$n"; cp -r "$dir"/. "$D/$n/"; echo "$n $dir" >>"$D/units.txt"
      done < <(find "$tmp" -mindepth 2 -maxdepth 2 -type d -name 'c.clif' | sort)
      echo "  dumps: units=$n unopt=$(find "$D" -name '*.unopt.clif' | wc -l) opt=$(find "$D" -name '*.opt.clif' | wc -l)"
      python3 "$B/notrap-dead.py" --json "$O/notrap-unopt.json" "$D" | sed 's/^/  notrap unopt: /'
      python3 "$B/notrap-dead.py" --suffix .opt.clif "$D" | sed 's/^/  notrap opt: /'
    fi
    rm -rf "$d/target/$p"
  done
  rm -rf "$d"
done
rm -rf "$act"

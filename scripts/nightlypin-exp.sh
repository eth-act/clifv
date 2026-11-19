#!/usr/bin/env bash
# NightlyPin1 experiment (agent/NightlyPin1 only, not for main): the same nightly's cg_clif
# linked against Cranelift 0.135.0 (as shipped) and against 0.136.1 (FV_CG_CLIF_CRANELIFT,
# scripts/build-cg-clif.sh). For each example and profile, `examples/compare.sh … --lean-link
# --verified --keep-temps` with each cg_clif, then
#   - crate parity (Lean vs that cg_clif): scripts/stock-crate-parity.py
#   - per function across the two runs: scripts/nightlypin-s2s.py
# Both cg_clif builds are copied to the same path before their run (target/cg_clif-active): the
# backend's path is part of RUSTFLAGS, which feeds cargo's -C metadata and so the symbol names.
#
#   scripts/nightlypin-exp.sh OUT [example:profile …]    e.g. fv-demo:debug survey:release
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$1; shift
mkdir -p "$out"
export PATH="$root/rust/target/release:$PATH" FV_ROOT="$root"
act=$root/target/cg_clif-active
for ep in "$@"; do
  ex=${ep%%:*}; prof=${ep##*:}
  rel=()
  [[ $prof == release ]] && rel=(--release)
  for cl in 0.135.0 0.136.1; do
    d=cg_clif; [[ $cl == 0.136.1 ]] && d=cg_clif-cl0.136.1
    rm -rf "$act" && mkdir -p "$act" && cp -r "$root/target/$d/unwind" "$root/target/$d/abort" "$act/"
    tag=$ex-$prof-$cl
    rm -rf "$root/examples/$ex/target"
    FV_CG_CLIF=$act/unwind/librustc_codegen_cranelift.so \
      "$root/examples/compare.sh" "$root/examples/$ex" --lean-link --verified --keep-temps "${rel[@]}" \
      >"$out/$tag.compare.log" 2>&1
    echo "$tag compare rc=$?: $(grep -E '^SAME|^DIFFERENT' "$out/$tag.compare.log")"
    grep -E '^cargo fv: [0-9]+ of [0-9]+ functions|^cargo fv: binary check|^  total' "$out/$tag.compare.log" | sed "s/^/  $tag: /" | cut -c1-260
    tmpd=$(ls -d "$root/examples/$ex"/target/fv/*/tmp 2>/dev/null | head -1)
    python3 "$root/scripts/stock-crate-parity.py" --json "$out/$tag.parity.json" "$tmpd" >"$out/$tag.parity.txt" 2>&1
    echo "  $tag parity: $(grep -m1 '^functions' "$out/$tag.parity.txt")"
    rm -rf "$out/keep-$tag" && mkdir -p "$out/keep-$tag"
    (cd "$tmpd" && find . -maxdepth 2 \( -name cgclif.o -o -name lean.o -o -name c.clif \) \
      -exec cp -r --parents {} "$out/keep-$tag/" \;)
    cp "$root/examples/$ex/target/fv-report.json" "$out/$tag.fv-report.json" 2>/dev/null
  done
  # the CLIF of the dumps (c.clif dirs of all CGUs; lines sorted, CGU prefixes removed): the same
  # in both runs? (Lean compiles the unoptimised dumps; *.opt.clif is Cranelift's mid-end output)
  set -f
  for sel in "! -name *.opt.clif" "-name *.opt.clif"; do
    for cl in 0.135.0 0.136.1; do
      # shellcheck disable=SC2086
      find "$out/keep-$ex-$prof-$cl" -path '*/c.clif/*' -type f $sel -exec cat {} + |
        sed -E 's/_fv_[0-9a-f]{12}_//g' | LC_ALL=C sort | md5sum
    done | uniq -c | sed "s/^/  $ex-$prof c.clif ($sel) md5 (count, sum): /"
  done
  set +f
  python3 "$root/scripts/nightlypin-s2s.py" "$out/keep-$ex-$prof-0.135.0" "$out/keep-$ex-$prof-0.136.1" \
    --diffs "$out/s2s-$ex-$prof.diffs" --json "$out/s2s-$ex-$prof.json" >"$out/s2s-$ex-$prof.txt" 2>&1
  sed "s/^/  $ex-$prof s2s: /" "$out/s2s-$ex-$prof.txt"
done
rm -rf "$root"/examples/*/target "$act"

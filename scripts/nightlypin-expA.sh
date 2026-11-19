#!/usr/bin/env bash
# NightlyPin1 experiment, option A (agent/NightlyPin1 only, not for main): cargo fv with another
# nightly (FV_TOOLCHAIN/TOOLCHAIN) and that nightly's cg_clif (scripts/build-cg-clif.sh with
# FV_TOOLCHAIN set, output target/cg_clif), with crate parity and the fallback reasons.
#
#   FV_TOOLCHAIN=nightly-2026-10-24 scripts/nightlypin-expA.sh OUT [example:profile …]
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$1; shift
mkdir -p "$out"
export PATH="$root/rust/target/release:$PATH" FV_ROOT="$root" TOOLCHAIN=$FV_TOOLCHAIN
for ep in "$@"; do
  ex=${ep%%:*}; prof=${ep##*:}
  rel=()
  [[ $prof == release ]] && rel=(--release)
  tag=$ex-$prof-$FV_TOOLCHAIN
  rm -rf "$root/examples/$ex/target"
  FV_CG_CLIF=$root/target/cg_clif/unwind/librustc_codegen_cranelift.so \
    "$root/examples/compare.sh" "$root/examples/$ex" --lean-link --verified --keep-temps "${rel[@]}" \
    >"$out/$tag.compare.log" 2>&1
  echo "$tag compare rc=$?: $(grep -E '^SAME|^DIFFERENT' "$out/$tag.compare.log")"
  grep -E '^cargo fv: [0-9]+ of [0-9]+ functions|^cargo fv: binary check|^  total|^cargo test|^cargo fv test' \
    "$out/$tag.compare.log" | sed "s/^/  $tag: /" | cut -c1-260
  tmpd=$(ls -d "$root/examples/$ex"/target/fv/*/tmp 2>/dev/null | head -1)
  python3 "$root/scripts/stock-crate-parity.py" --json "$out/$tag.parity.json" "$tmpd" >"$out/$tag.parity.txt" 2>&1
  echo "  $tag parity: $(grep -m1 '^functions' "$out/$tag.parity.txt")"
  cp "$root/examples/$ex/target/fv-report.json" "$out/$tag.fv-report.json" 2>/dev/null
  rm -rf "$out/keep-$tag" && mkdir -p "$out/keep-$tag"
  (cd "$tmpd" && find . -maxdepth 2 -name c.clif -exec cp --parents {} "$out/keep-$tag/" \;)
done
rm -rf "$root"/examples/*/target

#!/usr/bin/env bash
# NightlyPin1 experiment (agent/NightlyPin1 only, not for main): the same nightly's cg_clif
# linked against Cranelift 0.135.0 (as shipped) and against 0.136.1 (FV_CG_CLIF_CRANELIFT,
# scripts/build-cg-clif.sh). For each example and profile, `examples/compare.sh … --lean-link
# --verified --keep-temps` with each cg_clif, then
#   - crate parity (Lean vs that cg_clif): scripts/stock-crate-parity.py
#   - stock vs stock (cg_clif 0.136.1's object vs cg_clif 0.135.0's, every function): the same
#     script on CGU dirs whose `lean.o` is the 0.136.1 `cgclif.o`
#
#   scripts/nightlypin-exp.sh OUT [example:profile …]    e.g. fv-demo:debug survey:release
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$1; shift
mkdir -p "$out"
export PATH="$root/rust/target/release:$PATH" FV_ROOT="$root"
for ep in "$@"; do
  ex=${ep%%:*}; prof=${ep##*:}
  rel=()
  [[ $prof == release ]] && rel=(--release)
  for cl in 0.135.0 0.136.1; do
    d=cg_clif; [[ $cl == 0.136.1 ]] && d=cg_clif-cl0.136.1
    tag=$ex-$prof-$cl
    rm -rf "$root/examples/$ex/target"
    FV_CG_CLIF=$root/target/$d/unwind/librustc_codegen_cranelift.so \
      "$root/examples/compare.sh" "$root/examples/$ex" --lean-link --verified --keep-temps "${rel[@]}" \
      >"$out/$tag.compare.log" 2>&1
    echo "$tag compare rc=$?: $(grep -E '^SAME|^DIFFERENT' "$out/$tag.compare.log")"
    grep -E '^cargo fv:|^  total' "$out/$tag.compare.log" | head -12 | sed "s/^/  $tag: /"
    tmpd=$(ls -d "$root/examples/$ex"/target/fv/*/tmp 2>/dev/null | head -1)
    python3 "$root/scripts/stock-crate-parity.py" --json "$out/$tag.parity.json" "$tmpd" >"$out/$tag.parity.txt" 2>&1
    echo "  $tag parity: $(grep -m1 '^functions' "$out/$tag.parity.txt")"
    rm -rf "$out/keep-$tag" && mkdir -p "$out/keep-$tag"
    (cd "$tmpd" && find . \( -name cgclif.o -o -name lean.o \) -exec cp --parents {} "$out/keep-$tag/" \;)
  done
  # stock vs stock: every function of 0.136.1's cg_clif object against 0.135.0's
  s=$out/s2s-$ex-$prof; rm -rf "$s"; mkdir -p "$s"
  (cd "$out/keep-$ex-$prof-0.135.0" && find . -name cgclif.o) | while read -r f; do
    g=$out/keep-$ex-$prof-0.136.1/$f
    [[ -f $g ]] || continue
    c=$s/$(dirname "$f" | tr / _)
    mkdir -p "$c" && cp "$out/keep-$ex-$prof-0.135.0/$f" "$c/cgclif.o" && cp "$g" "$c/lean.o"
  done
  python3 "$root/scripts/stock-crate-parity.py" --json "$out/s2s-$ex-$prof.json" "$s"/* >"$out/s2s-$ex-$prof.txt" 2>&1
  echo "$ex-$prof stock 0.136.1 vs stock 0.135.0: $(grep -m1 '^functions' "$out/s2s-$ex-$prof.txt")"
  rm -rf "$s"
done
rm -rf "$root"/examples/*/target

#!/usr/bin/env bash
# NightlyPin1 experiment (agent/NightlyPin1 only, not for main): which committed crate proofs
# change when cg_clif links Cranelift 0.136.1 instead of 0.135.0? Runs scripts/regen-crate-proofs.sh
# with target/cg_clif/{unwind,abort} as built (0.135.0) and again with the 0.136.1 builds
# (target/cg_clif-cl0.136.1) in their place, records `git diff --stat` of crate-proofs for each, and
# restores the tree and target/cg_clif.
#
#   scripts/nightlypin-regen.sh OUT
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$1
mkdir -p "$out"
cd "$root"
regen() {
  FV_ROOT=$root scripts/regen-crate-proofs.sh >"$out/regen-$1.log" 2>&1
  echo "regen with cg_clif $1: rc=$?"
  git add -N crate-proofs
  git diff --stat -- crate-proofs >"$out/regen-$1.stat"
  git diff -- crate-proofs >"$out/regen-$1.diff"
  echo "  $(tail -1 "$out/regen-$1.stat")"
  git checkout -q -- crate-proofs
  git reset -q
  git clean -fdq crate-proofs/Crates
}
regen 0.135.0
save=$root/target/cg_clif-save
rm -rf "$save" && mkdir -p "$save"
mv target/cg_clif/unwind target/cg_clif/abort "$save/"
cp -r target/cg_clif-cl0.136.1/unwind target/cg_clif-cl0.136.1/abort target/cg_clif/
regen 0.136.1
rm -rf target/cg_clif/unwind target/cg_clif/abort
mv "$save"/unwind "$save"/abort target/cg_clif/
rmdir "$save"
git status --short -- crate-proofs | head -3

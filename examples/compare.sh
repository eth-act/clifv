#!/usr/bin/env bash
# Run a crate's (or workspace's) tests twice and compare the per-test outcomes:
#   1. `cargo test` with rustc's LLVM backend (the pinned nightly, aarch64-unknown-linux-musl,
#      run under qemu-aarch64-static; target dir target/llvm), the reference;
#   2. `cargo fv test [FV_ARGS…]` (cg_clif + the Lean backend).
# Exit 0 iff both runs pass and report the same tests with the same outcomes.
#
#   examples/compare.sh DIR [FV_ARGS…]     e.g. examples/compare.sh examples/survey --release
# `cargo fv` must be on PATH (rust/target/release, see docs/USAGE.md).
set -uo pipefail
dir=$(cd "$1" && pwd); shift
tc=${TOOLCHAIN:-nightly-2026-09-26}
tmp=$(mktemp -d /tmp/fv-compare.XXXXXX)
outcomes() { # cargo test output -> "binary-stem test-name outcome" lines, sorted
  awk '/^ *Running /{ n = split($2, p, "/"); b = p[n]; sub(/-[0-9a-f]+$/, "", b) }
       /^ *Doc-tests /{ b = "doctests-" $2 }
       /^test .* \.\.\. / { sub(/ - should panic/, ""); print b, $2, $NF }' "$1" | sort
}
release=()
for a in "$@"; do [[ "$a" == --release || "$a" == -r ]] && release=(--release); done
(cd "$dir" && CARGO_TARGET_DIR="$dir/target/llvm" \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=rust-lld \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER=qemu-aarch64-static \
  cargo +"$tc" test "${release[@]}" --workspace --target aarch64-unknown-linux-musl) >"$tmp/llvm.log" 2>&1
llvm=$?
(cd "$dir" && cargo fv test --workspace "$@") >"$tmp/fv.log" 2>&1
fv=$?
outcomes "$tmp/llvm.log" >"$tmp/llvm.txt"
outcomes "$tmp/fv.log" >"$tmp/fv.txt"
grep -E '^  (package|total|[A-Za-z0-9_-]+ +(lib|test|bin) )' "$tmp/fv.log"
grep '^cargo fv:' "$tmp/fv.log"
echo "cargo test (LLVM):   exit $llvm, $(grep -c ' ok$' "$tmp/llvm.txt") ok, $(grep -vc ' ok$' "$tmp/llvm.txt") not ok"
echo "cargo fv test:       exit $fv, $(grep -c ' ok$' "$tmp/fv.txt") ok, $(grep -vc ' ok$' "$tmp/fv.txt") not ok"
if [[ $llvm -eq 0 && $fv -eq 0 ]] && diff -u "$tmp/llvm.txt" "$tmp/fv.txt"; then
  echo "SAME: $(wc -l <"$tmp/fv.txt") test outcomes identical (logs: $tmp)"
  exit 0
fi
diff -u "$tmp/llvm.txt" "$tmp/fv.txt" | head -40
echo "DIFFERENT or failing (logs: $tmp)"
exit 1

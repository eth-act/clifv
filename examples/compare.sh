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
       /^test .* \.\.\. / { sub(/ - should panic/, ""); i = index($0, " ... "); print b, $2, substr($0, i + 5) }' "$1" | sort
}
release=()
for a in "$@"; do [[ "$a" == --release || "$a" == -r ]] && release=(--release); done
(cd "$dir" && CARGO_TARGET_DIR="$dir/target/llvm" \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=rust-lld \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER=qemu-aarch64-static \
  cargo +"$tc" test "${release[@]}" --workspace --no-fail-fast --target aarch64-unknown-linux-musl) >"$tmp/llvm.log" 2>&1
llvm=$?
(cd "$dir" && cargo fv test --workspace --no-fail-fast "$@") >"$tmp/fv.log" 2>&1
fv=$?
outcomes "$tmp/llvm.log" >"$tmp/llvm.txt"
outcomes "$tmp/fv.log" >"$tmp/fv.txt"
grep -E '^  (package|total|[A-Za-z0-9_-]+ +(lib|test|bin) )' "$tmp/fv.log"
grep '^cargo fv:' "$tmp/fv.log"
counts() { echo "$(grep -c ' ok$' "$1") ok, $(grep -c ' ignored' "$1") ignored, $(grep -vc ' ok$\| ignored' "$1") failed"; }
echo "cargo test (LLVM):   exit $llvm, $(counts "$tmp/llvm.txt")"
echo "cargo fv test:       exit $fv, $(counts "$tmp/fv.txt")"
if [[ $llvm -eq 0 && $fv -eq 0 ]] && diff -u "$tmp/llvm.txt" "$tmp/fv.txt"; then
  echo "SAME: $(wc -l <"$tmp/fv.txt") test outcomes identical (logs: $tmp)"
  exit 0
fi
diff -u "$tmp/llvm.txt" "$tmp/fv.txt" | head -40
echo "DIFFERENT or failing (logs: $tmp)"
exit 1

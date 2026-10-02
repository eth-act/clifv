#!/usr/bin/env bash
# Run a crate's (or workspace's) tests twice and compare the per-test outcomes:
#   1. the reference: `cargo test` with rustc's LLVM backend (default, BASELINE=llvm; target dir
#      target/llvm) or, with BASELINE=cg_clif, with plain rustc_codegen_cranelift — the same
#      cg_clif `cargo fv` uses (FV_CG_CLIF, else with panic=unwind target/cg_clif-unwind/… if
#      built, else the shipped one; target dir target/cg_clif). Both use the pinned nightly,
#      aarch64-unknown-linux-musl, qemu-aarch64-static, and the panic strategy of the fv run
#      (unwind, or abort with --panic-abort);
#   2. `cargo fv test [FV_ARGS…]` (cg_clif + the Lean backend).
# BASELINE=llvm: exit 0 iff both runs pass and report the same tests with the same outcomes.
# BASELINE=cg_clif: exit 0 iff both runs report the same outcomes and both pass or both fail
# (the shipped cg_clif has no landing pads, so catch_unwind/Drop-during-unwinding tests fail
# under plain cg_clif too; cargo fv must not change that).
#
#   examples/compare.sh DIR [FV_ARGS…]     e.g. examples/compare.sh examples/survey --release
# `cargo fv` must be on PATH (rust/target/release, see docs/USAGE.md).
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$(cd "$1" && pwd); shift
tc=${TOOLCHAIN:-nightly-2026-09-26}
baseline=${BASELINE:-llvm}
tmp=$(mktemp -d /tmp/fv-compare.XXXXXX)
outcomes() { # cargo test output -> "binary-stem test-name outcome" lines, sorted
  awk '/^ *Running /{ n = split($2, p, "/"); b = p[n]; sub(/-[0-9a-f]+$/, "", b) }
       /^ *Doc-tests /{ b = "doctests-" $2 }
       /^test .* \.\.\. / { sub(/ - should panic/, ""); i = index($0, " ... "); print b, $2, substr($0, i + 5) }' "$1" | sort
}
release=()
panic=()
for a in "$@"; do
  [[ "$a" == --release || "$a" == -r ]] && release=(--release)
  [[ "$a" == --panic-abort ]] && panic=(-Cpanic=abort -Zpanic-abort-tests)
done
case "$baseline" in
  llvm) flags="${panic[*]}"; tdir=llvm ;;
  cg_clif)
    backend=${FV_CG_CLIF:-}
    [[ -z "$backend" && ${#panic[@]} -eq 0 && -f "$root/target/cg_clif-unwind/librustc_codegen_cranelift.so" ]] &&
      backend=$root/target/cg_clif-unwind/librustc_codegen_cranelift.so
    backend=${backend:-cranelift}
    flags="-Zcodegen-backend=$backend ${panic[*]}"; tdir=cg_clif ;;
  *) echo "BASELINE must be llvm or cg_clif" >&2; exit 2 ;;
esac
(cd "$dir" && CARGO_TARGET_DIR="$dir/target/$tdir" RUSTFLAGS="$flags" RUSTDOCFLAGS="${panic[*]}" \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER=rust-lld \
  CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER=qemu-aarch64-static \
  cargo +"$tc" test "${release[@]}" --workspace --no-fail-fast --target aarch64-unknown-linux-musl) >"$tmp/ref.log" 2>&1
ref=$?
(cd "$dir" && cargo fv test --workspace --no-fail-fast "$@") >"$tmp/fv.log" 2>&1
fv=$?
outcomes "$tmp/ref.log" >"$tmp/ref.txt"
outcomes "$tmp/fv.log" >"$tmp/fv.txt"
grep -E '^  (package|total|your crate|dependencies|std |exe |  Lean in exe per|[A-Za-z0-9_-]+ +(lib|test|bin|dep) )' "$tmp/fv.log"
grep -E '^cargo fv:|^  panic=' "$tmp/fv.log"
counts() { echo "$(grep -c ' ok$' "$1") ok, $(grep -c ' ignored' "$1") ignored, $(grep -vc ' ok$\| ignored' "$1") failed"; }
echo "cargo test ($baseline): exit $ref, $(counts "$tmp/ref.txt")"
echo "cargo fv test:       exit $fv, $(counts "$tmp/fv.txt")"
if [[ "$baseline" == llvm ]]; then
  status_ok=$([[ $ref -eq 0 && $fv -eq 0 ]] && echo 1)
else
  status_ok=$([[ $((ref == 0)) == $((fv == 0)) ]] && echo 1)
fi
if [[ -n "$status_ok" ]] && diff -u "$tmp/ref.txt" "$tmp/fv.txt"; then
  echo "SAME: $(wc -l <"$tmp/fv.txt") test outcomes identical (logs: $tmp)"
  exit 0
fi
diff -u "$tmp/ref.txt" "$tmp/fv.txt" | head -40
echo "DIFFERENT or failing (logs: $tmp)"
exit 1

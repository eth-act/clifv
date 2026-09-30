#!/usr/bin/env bash
# Build rustc_codegen_cranelift (cg_clif) with its `unwinding` cargo feature, for the pinned
# nightly, into target/cg_clif-unwind/librustc_codegen_cranelift.so. `cargo fv` uses it
# when it exists (FV_CG_CLIF overrides; docs/USAGE.md, "Panics").
#
# The shipped `rustc-codegen-cranelift-preview` component is built without that feature: it
# skips cleanup blocks and compiles `catch_unwind` as a plain call, so Drop does not run during
# unwinding and `catch_unwind` in cg_clif-compiled code does not catch. With the feature, cg_clif
# emits `try_call` + landing pads and LSDAs (.gcc_except_table), like LLVM.
#
# Recipe: the cg_clif sources of the nightly's own rustc commit (`rustc -vV` commit-hash,
# a sparse, shallow checkout of rust-lang/rust's compiler/rustc_codegen_cranelift), built with
# the nightly's `rustc-dev` component (rustc_private crates) and linked against the nightly's
# libLLVM (`-L native=<sysroot>/lib`). Needs network access the first time (~40 s build).
#
#   scripts/build-cg-clif-unwind.sh      (run it through scripts/memcap.sh on shared machines)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TC=${FV_TOOLCHAIN:-nightly-2026-09-26}
OUT=$ROOT/target/cg_clif-unwind
SRC=$OUT/rust
commit=$(rustc +"$TC" -vV | sed -n 's/^commit-hash: //p')
[[ -n "$commit" ]] || { echo "no commit-hash in rustc +$TC -vV" >&2; exit 1; }
rustup component add rustc-dev --toolchain "$TC"
mkdir -p "$OUT"
if [[ ! -d "$SRC/.git" ]]; then
  git init -q "$SRC"
  git -C "$SRC" remote add origin https://github.com/rust-lang/rust.git
  git -C "$SRC" sparse-checkout set --no-cone /compiler/rustc_codegen_cranelift/
fi
if [[ "$(git -C "$SRC" rev-parse -q --verify HEAD 2>/dev/null)" != "$commit" ]]; then
  git -C "$SRC" fetch -q --depth 1 --filter=blob:none origin "$commit"
  git -C "$SRC" checkout -q --detach FETCH_HEAD
fi
sysroot=$(rustc +"$TC" --print sysroot)
(cd "$SRC/compiler/rustc_codegen_cranelift" &&
  RUSTFLAGS="-L native=$sysroot/lib" CARGO_TARGET_DIR="$OUT/target" \
    cargo +"$TC" build --release --locked --features unwinding)
cp "$OUT/target/release/librustc_codegen_cranelift.so" "$OUT/librustc_codegen_cranelift.so"
echo "built $OUT/librustc_codegen_cranelift.so (cg_clif of rustc $commit, features: unwinding)"

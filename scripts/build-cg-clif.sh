#!/usr/bin/env bash
# Build rustc_codegen_cranelift (cg_clif) for the pinned nightly with this repository's patch
# scripts/patches/cg-clif-extnames.patch, in two variants:
#
#   target/cg_clif/unwind/librustc_codegen_cranelift.so   (cargo feature `unwinding`)
#   target/cg_clif/abort/librustc_codegen_cranelift.so    (without it)
#
# `cargo fv` uses the first with panic=unwind and the second with panic=abort (FV_CG_CLIF
# overrides; docs/USAGE.md, "Install" and "Panics"). It needs one of them: the shipped
# `rustc-codegen-cranelift-preview` component does not write the tables below.
#
# The patch (pretty_clif.rs `write_ext_names`) appends to every CLIF dump cg_clif writes
# (`*.unopt.clif`, `*.opt.clif`) the function's external-name table and the module's
# declarations of the names it uses — which symbol each `userextnameJ`, `u0:N` and libcall
# denotes (docs/contracts/frontend.md, FV/Front/Raw.lean). It changes no code cg_clif emits.
#
# The `unwinding` feature: the shipped component is built without it: it skips cleanup blocks
# and compiles `catch_unwind` as a plain call, so Drop does not run during unwinding and
# `catch_unwind` in cg_clif-compiled code does not catch. With the feature, cg_clif emits
# `try_call` + landing pads and LSDAs (.gcc_except_table), like LLVM. With panic=abort it would
# turn every call that may unwind into a `try_call` with a terminate edge, hence the second
# variant.
#
# Recipe: the cg_clif sources of the nightly's own rustc commit (`rustc -vV` commit-hash, a
# sparse, shallow checkout of rust-lang/rust's compiler/rustc_codegen_cranelift), the patch
# applied, built with the nightly's `rustc-dev` component (rustc_private crates) and linked
# against the nightly's libLLVM (`-L native=<sysroot>/lib`). Needs network access the first
# time (~40 s per variant).
#
#   scripts/build-cg-clif.sh      (run it through scripts/memcap.sh on shared machines)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TC=${FV_TOOLCHAIN:-nightly-2026-09-26}
OUT=$ROOT/target/cg_clif
SRC=$OUT/rust
PATCH=$ROOT/scripts/patches/cg-clif-extnames.patch
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
  git -C "$SRC" checkout -q --force --detach FETCH_HEAD
fi
# the patch, exactly: reset the patched files, then apply
git -C "$SRC" checkout -q -- compiler/rustc_codegen_cranelift
git -C "$SRC" apply "$PATCH"
sysroot=$(rustc +"$TC" --print sysroot)
for variant in unwind abort; do
  features=()
  [[ $variant == unwind ]] && features=(--features unwinding)
  (cd "$SRC/compiler/rustc_codegen_cranelift" &&
    RUSTFLAGS="-L native=$sysroot/lib" CARGO_TARGET_DIR="$OUT/target" \
      cargo +"$TC" build --release --locked "${features[@]}")
  mkdir -p "$OUT/$variant"
  cp "$OUT/target/release/librustc_codegen_cranelift.so" "$OUT/$variant/librustc_codegen_cranelift.so"
  echo "built $OUT/$variant/librustc_codegen_cranelift.so (cg_clif of rustc $commit, patched, ${features[*]:-no features})"
done

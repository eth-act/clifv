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
#
# Experiment (agent/NightlyPin1, not for main): FV_CG_CLIF_CRANELIFT=0.136.1 builds the same
# nightly's cg_clif against that Cranelift version instead of the one its Cargo.lock pins
# (output target/cg_clif-cl<version>/…; API adaptations in scripts/patches/cg-clif-cl<version>.patch
# when that file exists).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
TC=${FV_TOOLCHAIN:-nightly-2026-09-26}
CL=${FV_CG_CLIF_CRANELIFT:-}
OUT=${FV_CG_CLIF_OUT:-$ROOT/target/cg_clif${CL:+-cl$CL}}
SRC=$OUT/rust
PATCH=$ROOT/scripts/patches/cg-clif-extnames.patch
CLPATCH=$ROOT/scripts/patches/cg-clif-cl$CL.patch
commit=$(rustc +"$TC" -vV | sed -n 's/^commit-hash: //p')
[[ -n "$commit" ]] || { echo "no commit-hash in rustc +$TC -vV" >&2; exit 1; }
rustup component add rustc-dev rust-src --toolchain "$TC"
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
if [[ -n "$CL" ]]; then
  cg="$SRC/compiler/rustc_codegen_cranelift"
  sed -i -E "s/^(cranelift-[a-z]+ = \{ version = \")[0-9.]+\"/\1=$CL\"/" "$cg/Cargo.toml"
  # cranelift-object 0.136.x writes with object 0.40 (cg_clif's own upstream update to 0.137
  # made the same change)
  sed -i -E 's/^(object = \{ version = ")0\.39\.1"/\10.40.0"/' "$cg/Cargo.toml"
  grep -E '^(cranelift-|object)' "$cg/Cargo.toml"
  (cd "$cg" && cargo +"$TC" update -p cranelift-codegen -p cranelift-frontend -p cranelift-module \
    -p cranelift-native -p cranelift-jit -p cranelift-object)
  # cranelift-codegen's own dependencies on -meta/-shared/-control/-srcgen are caret
  # requirements: pin every cranelift-* crate to exactly $CL, as rust/Cargo.lock does (several
  # passes: a crate can only be downgraded once the crates requiring a newer one are)
  off() { awk '/^name = "cranelift-/{n=$3; getline; if ($3 != "\"'"$CL"'\"") print n}' "$cg/Cargo.lock" | tr -d '"'; }
  for _ in 1 2 3 4 5; do
    for p in $(off); do (cd "$cg" && cargo +"$TC" update -q -p "$p" --precise "$CL") || true; done
  done
  [[ -z "$(off)" ]] || { echo "not pinned to $CL: $(off)" >&2; exit 1; }
  if [[ -f "$CLPATCH" ]]; then git -C "$SRC" apply "$CLPATCH"; fi
fi
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
# `cargo fv --build-std`: the standard library's sources (the toolchain's `rust-src`) with
# cg_clif's own `stdlib` patches, which cg_clif applies to the sysroot it builds for itself
# (0027: the 128-bit atomic types are removed; cg_clif cannot compile 128-bit atomics)
rm -rf "$OUT/std-src.tmp" && mkdir -p "$OUT/std-src.tmp"
cp -r "$sysroot/lib/rustlib/src/rust/library" "$OUT/std-src.tmp/"
for p in "$SRC"/compiler/rustc_codegen_cranelift/patches/*-stdlib-*.patch; do
  patch -s -p1 -d "$OUT/std-src.tmp" <"$p"
done
rm -rf "$OUT/std-src" && mv "$OUT/std-src.tmp" "$OUT/std-src"
echo "prepared $OUT/std-src/library (rust-src of $TC with cg_clif's stdlib patches, for cargo fv --build-std)"

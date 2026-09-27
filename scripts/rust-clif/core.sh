#!/usr/bin/env bash
# Dump the CLIF cg_clif produces for `core` and `alloc` themselves (-Zbuild-std, release),
# i.e. the non-generic library code a Rust program links against (panicking, fmt, float
# printing/parsing, unicode, str, …). compiler_builtins and build scripts are compiled with
# LLVM (cg_clif cannot compile compiler_builtins' f128 code). Target x86_64: on aarch64, cg_clif
# rejects core's 128-bit atomics ("128bit atomics not yet supported").
#
# usage: scripts/rust-clif/core.sh [WORK_DIR]     (default /tmp/rust-clif-survey/core)
# Result: WORK_DIR/clif/{core,alloc} (symlinks to cg_clif's `.clif` directories).
set -euo pipefail

TOOLCHAIN=${TOOLCHAIN:-nightly-2026-09-26}
work=${1:-/tmp/rust-clif-survey/core}
rm -rf "$work"
mkdir -p "$work"
cd "$work"
cat >Cargo.toml <<'EOF'
[package]
name = "corelib-probe"
version = "0.1.0"
edition = "2021"
[lib]
path = "lib.rs"
[profile.release]
panic = "abort"
EOF
printf '#![no_std]\nextern crate alloc;\npub fn f(x: u32) -> alloc::vec::Vec<u32> { alloc::vec![x] }\n' >lib.rs
cat >wrap.sh <<'EOF'
#!/usr/bin/env bash
# RUSTC_WRAPPER: cg_clif + CLIF dump for every crate except compiler_builtins and build scripts.
# Several CGUs, so rustc does not try to copy the `.ll` file cg_clif never writes.
rustc="$1"; shift
for a in "$@"; do
  [[ "$a" == compiler_builtins || "$a" == build_script_build ]] && exec "$rustc" "$@"
done
exec "$rustc" "$@" -Zcodegen-backend=cranelift --emit=llvm-ir -Zunstable-options \
  -Csymbol-mangling-version=hashed -Ccodegen-units=16
EOF
chmod +x wrap.sh
# The final probe crate fails (single CGU, `.ll` copy); core and alloc are complete by then.
RUSTC_WRAPPER="$work/wrap.sh" cargo +"$TOOLCHAIN" build --release -Zbuild-std=core,alloc \
  --target x86_64-unknown-linux-gnu >build.log 2>&1 || true
if grep -q 'error writing ir file' build.log; then echo "core.sh: some CLIF files were not written" >&2; exit 1; fi
mkdir -p clif
for c in core alloc; do
  ln -sfn "$(ls -d "$work"/target/x86_64-unknown-linux-gnu/release/build/$c/*/out/$c-*.clif)" "clif/$c"
  echo "$c: $(ls "clif/$c/" | grep -c '\.unopt\.clif$') functions"
done

#!/usr/bin/env bash
# Compile the survey corpus (scripts/rust-clif/corpus/*.rs) with rustc_codegen_cranelift and
# dump the CLIF it produces.
#
# usage: scripts/rust-clif/dump.sh [OUT_DIR]      (default /tmp/rust-clif-survey/out)
#
# Output: OUT_DIR/<profile>/<crate>/<crate>.clif/<symbol>.{unopt,opt}.clif (+ .vcode),
#         OUT_DIR/<profile>/<crate>/<crate>.o and <crate>.undef (undefined symbols of the object).
#
# cg_clif writes CLIF files whenever `llvm-ir` is among the requested outputs
# (`pretty_clif::should_write_ir`): `*.unopt.clif` is the frontend's output (after
# FunctionBuilder::finalize, before Cranelift's mid-end), `*.opt.clif` is `context.func` after
# `Context::compile` (egraph mid-end at opt_level=speed_and_size, legalisation). rustc then fails
# to copy the `.ll` file cg_clif never writes; that error (exit 1) is expected and ignored.
# Symbols use `hashed` mangling: cg_clif names each file after the symbol and v0 names of
# monomorphised iterator adapters exceed the 255-byte file-name limit. `#[no_mangle]` functions
# keep their names; every file's `; instance` comment still names the Rust item.
set -euo pipefail

TOOLCHAIN=${TOOLCHAIN:-nightly-2026-09-26}
TARGET=${TARGET:-aarch64-unknown-linux-gnu}
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-/tmp/rust-clif-survey/out}

declare -A PROFILE=(
  [debug]="-Copt-level=0 -Cdebug-assertions=on -Coverflow-checks=on"
  [release]="-Copt-level=3 -Cdebug-assertions=off -Coverflow-checks=off"
  [release-oc]="-Copt-level=3 -Cdebug-assertions=off -Coverflow-checks=on"
)

for prof in debug release release-oc; do
  for src in "$here"/corpus/*.rs; do
    crate=$(basename "$src" .rs)
    dir="$out/$prof/$crate"
    rm -rf "$dir"
    mkdir -p "$dir"
    # shellcheck disable=SC2086
    if ! rustc +"$TOOLCHAIN" -Zcodegen-backend=cranelift --target "$TARGET" \
        --edition 2021 --crate-type lib --crate-name "$crate" -Cpanic=abort \
        -Zunstable-options -Csymbol-mangling-version=hashed -Ccodegen-units=1 ${PROFILE[$prof]} \
        --emit=llvm-ir,obj --out-dir "$dir" "$src" 2>"$dir/rustc.stderr"; then
      if grep -v -e 'could not copy .*\.ll' -e 'aborting due to 1 previous error' \
          "$dir/rustc.stderr" | grep -q -e '^error' -e 'error writing ir file'; then
        cat "$dir/rustc.stderr" >&2
        echo "dump.sh: $prof/$crate failed" >&2
        exit 1
      fi
    fi
    nm -u "$dir/$crate.o" | awk '{print $2}' | sort -u >"$dir/$crate.undef"
    n=$(find "$dir/$crate.clif" -name '*.unopt.clif' | wc -l)
    echo "$prof/$crate: $n functions"
  done
done

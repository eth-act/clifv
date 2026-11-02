#!/usr/bin/env bash
# Build the pinned stock filetest compiler with an opt-in pre-JIT export hook.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
UPSTREAM=third_party/wasmtime
if [[ ! -e "$UPSTREAM" ]]; then
  git clone --depth 1 --branch v49.0.1 https://github.com/bytecodealliance/wasmtime "$UPSTREAM"
fi
test "$(git -C "$UPSTREAM" rev-parse HEAD)" = 46c23a87dac1465986a8ad53ba6a7ae49372857b
# The usual sparse fetch lacks dependencies of the actual upstream filetest runner.
if [[ ! -f "$UPSTREAM/src/lib.rs" ]]; then
  git -C "$UPSTREAM" sparse-checkout disable
fi
PATCH="$ROOT/scripts/patches/prejit-export.patch"
if git -C "$UPSTREAM" apply --check "$PATCH" >/dev/null 2>&1; then
  git -C "$UPSTREAM" apply "$PATCH"
elif ! git -C "$UPSTREAM" apply --reverse --check "$PATCH"; then
  echo 'prejit-export: upstream source differs from the expected instrumentation; preserve and inspect its changes' >&2
  exit 2
fi
RUST_VERSION=$(sed -n 's/^channel = "\([^"]*\)"/\1/p' rust/rust-toolchain.toml)
if [[ ${FV_COMPARE_MEMCAP:-1} == 0 ]]; then
  rustup run "$RUST_VERSION" cargo build --locked --manifest-path tools/prejit-export/Cargo.toml
else
  bash scripts/memcap.sh rustup run "$RUST_VERSION" cargo build --locked --manifest-path tools/prejit-export/Cargo.toml
fi

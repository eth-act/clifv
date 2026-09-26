#!/usr/bin/env bash
# Fetch pinned external sources into third_party/. See docs/PINS.md.
set -euo pipefail
cd "$(dirname "$0")/.."
WASMTIME_TAG=v49.0.1
WASMTIME_COMMIT=46c23a87dac1465986a8ad53ba6a7ae49372857b
if [ ! -d third_party/wasmtime ]; then
  git clone -q --depth 1 --branch "$WASMTIME_TAG" --filter=blob:none --sparse \
    https://github.com/bytecodealliance/wasmtime third_party/wasmtime
  git -C third_party/wasmtime sparse-checkout set cranelift
fi
test "$(git -C third_party/wasmtime rev-parse HEAD)" = "$WASMTIME_COMMIT"

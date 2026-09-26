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
LNSYM_COMMIT=5c05220ff970e3bdd7813ad0c9ef3741522c8b92
if [ ! -d third_party/lnsym-upstream ]; then
  git clone -q https://github.com/leanprover/LNSym third_party/lnsym-upstream
  git -C third_party/lnsym-upstream checkout -q "$LNSYM_COMMIT"
fi
test "$(git -C third_party/lnsym-upstream rev-parse HEAD)" = "$LNSYM_COMMIT"

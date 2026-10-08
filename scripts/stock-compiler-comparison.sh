#!/usr/bin/env bash
# One-command, pinned build + validation + complete stock-filetest measurement.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

usage() {
  printf '%s\n' \
    'Usage: bash scripts/stock-compiler-comparison.sh [--out DIR] [--jobs N] [--input FILE ...]' \
    '' \
    'Builds the pinned Rust allocator, Lean backend and stock exporter; runs validation;' \
    'then inventories and compares all official filetests (unless --input selects a pilot).' \
    'Requires git, rustup, Python >=3.11, a C/C++ toolchain, and Lean from lean-toolchain.' \
    'Put Lean/lake on PATH, or set LEAN_BIN_DIR to their directory.' \
    'FV_MEMCAP defaults to 16G. FV_COMPARE_MEMCAP=0 explicitly disables systemd memory caps.' \
    'Exit 10 with a finished results.json is a completed measurement, not suite equivalence.'
}

OUT="target/stock-compiler-comparison-$(date -u +%Y%m%dT%H%M%SZ)-$$"
JOBS=2
INPUTS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --help|-h) usage; exit 0 ;;
    --out|--jobs|--input)
      [[ $# -ge 2 ]] || { usage >&2; exit 2; }
      case "$1" in
        --out) OUT=$2 ;;
        --jobs) JOBS=$2 ;;
        --input) INPUTS+=(--input "$2") ;;
      esac
      shift 2 ;;
    *) printf 'Unknown option: %s\n' "$1" >&2; usage >&2; exit 2 ;;
  esac
done
[[ "$JOBS" =~ ^[1-9][0-9]*$ ]] || { printf 'jobs must be positive\n' >&2; exit 2; }
[[ ${FV_COMPARE_MEMCAP:-1} == 0 || ${FV_COMPARE_MEMCAP:-1} == 1 ]] || {
  printf 'FV_COMPARE_MEMCAP must be 0 or 1\n' >&2; exit 2;
}
[[ ! ${BLESS+x} ]] || { printf 'BLESS must be unset\n' >&2; exit 2; }
for tool in git rustup python3; do
  command -v "$tool" >/dev/null || { printf 'Missing prerequisite: %s\n' "$tool" >&2; exit 2; }
done
python3 -c 'import sys; assert sys.version_info >= (3,11), "Python >=3.11 required"'
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
for tool in lean lake; do
  command -v "$tool" >/dev/null || {
    printf 'Missing %s: install %s, or set LEAN_BIN_DIR\n' "$tool" "$(<lean-toolchain)" >&2; exit 2;
  }
done
LEAN_VERSION=$(sed 's/.*:v//' lean-toolchain)
lean --version | python3 -c 'import re,sys; v=re.search(r"version ([0-9.]+)",sys.stdin.read()); assert v and v[1]==sys.argv[1], "wrong Lean version"' "$LEAN_VERSION"
RUST_VERSION=$(sed -n 's/^channel = "\([^"]*\)"/\1/p' rust/rust-toolchain.toml)
OUT=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$OUT")
BUILD_LOGS="${OUT}.build-logs"
[[ ! -e "$OUT" && ! -e "$BUILD_LOGS" ]] || { printf 'Choose a fresh output directory: %s\n' "$OUT" >&2; exit 2; }
mkdir -p "$BUILD_LOGS"
export PYTHONDONTWRITEBYTECODE=1
export CARGO_BUILD_JOBS="$JOBS"
export LEAN_REGALLOC="$ROOT/rust/target/release/lean-regalloc"
# Pin paths and avoid inherited wrappers/flags compiling different infrastructure.
unset CARGO_TARGET_DIR RUSTFLAGS CARGO_ENCODED_RUSTFLAGS RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER

guard() {
  if [[ ${FV_COMPARE_MEMCAP:-1} == 0 ]]; then "$@"; else bash scripts/memcap.sh "$@"; fi
}
step() {
  local label=$1
  shift
  printf '%s\n' "Running $label"
  printf '%q ' "$@" > "$BUILD_LOGS/$label.command"
  printf '\n' >> "$BUILD_LOGS/$label.command"
  "$@" 2>&1 | tee "$BUILD_LOGS/$label.log"
}

step rust-toolchain rustup toolchain install "$RUST_VERSION" --profile minimal
{
  rustup run "$RUST_VERSION" rustc -vV
  rustup run "$RUST_VERSION" cargo --version
  lean --version
  lake --version
  python3 --version
  git rev-parse HEAD
  printf 'memory_cap_enabled=%s\n' "${FV_COMPARE_MEMCAP:-1}"
  printf 'memory_cap=%s\n' "${FV_MEMCAP:-16G}"
} > "$BUILD_LOGS/versions.txt"
step allocator guard rustup run "$RUST_VERSION" cargo build --locked --release --manifest-path rust/Cargo.toml -p lean-regalloc
step lean-backend guard lake build lean-backend lean-backend-lowering-trace lean-stock-lowering-compare lean-stock-lowering-test
step stock-exporter bash scripts/prejit-export-build.sh
step trace-validation guard python3 -m unittest discover -s scripts -p test_lowering_trace.py -v
step schedule-validation guard python3 -m unittest discover -s scripts -p test_stock_lowering_schedule.py -v
step validation guard python3 -m unittest discover -s scripts -p test_stock_compiler_compare.py -v
step pipeline-validation guard python3 -m unittest discover -s scripts -p test_stock_pipeline.py -v
step exporter-validation guard python3 -m unittest discover -s scripts -p test_stock_exporter.py -v

set +e
guard python3 scripts/stock-compiler-compare.py --out "$OUT" --jobs "$JOBS" "${INPUTS[@]}" 2>&1 | tee "$BUILD_LOGS/comparison.log"
RESULTS=("${PIPESTATUS[@]}")
set -e
if [[ ${RESULTS[1]} != 0 ]]; then exit "${RESULTS[1]}"; fi
if [[ -f "$OUT/results.json" ]]; then
  python3 -c 'import json,sys; from pathlib import Path; p=Path(sys.argv[1]); r=json.loads((p/"results.json").read_text()); assert r["progress"]=="finished"; print("Measurement complete:",p/"summary.md"); print("Build/validation logs:",sys.argv[2])' "$OUT" "$BUILD_LOGS"
fi
exit "${RESULTS[0]}"

#!/usr/bin/env bash
# Run Cranelift's integer runtests natively: compile with Cranelift for aarch64 (clif2obj
# settings), execute every `; run:` line under qemu-aarch64-static (clif-native), check the
# outcomes against the expectations and, with --compare, against the Cranelift interpreter
# (clif-oracle). See docs/contracts/drivers.md.
#
# usage: scripts/aarch64-native-filetests.sh [-v] [--compare] [--all | FILE.clif...]
#   default files: the runtests that clif-filetest reports fully supported by Clif.run
#   (list below; regenerate with `.lake/build/bin/clif-filetest runtests/*.clif` and keep
#   the files with "unsupported 0"); --all: every file in runtests/.
#   -v: list every failing/erroring run (and every disagreement with --compare).
#
# Exit status 0 iff every run passes (no fail, error or file error) and, with --compare,
# every outcome agrees with the interpreter.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
RUNTESTS=third_party/wasmtime/cranelift/filetests/filetests/runtests

SUPPORTED="alias-analysis-endianness alias amode-shared-base arithmetic-extends arithmetic
atomic-128-cas-lse atomic-128 atomic-cas-little atomic-cas-subword-big
atomic-cas-subword-little atomic-cas atomic-load-store atomic-rmw-little atomic-rmw-subword-big
atomic-rmw-subword-little bitops bitrev bitselect bmask bnot br br_table brif cls clz const ctz
div-checks extend fence fibonacci fold-bitops global_value i128-arithmetic-extends
i128-arithmetic i128-bandnot i128-bitcast i128-bitops-count i128-bitops i128-bitrev
i128-bitselect i128-bmask i128-bnot i128-bornot i128-br i128-bswap i128-bxornot i128-call
i128-concat-split i128-extend i128-iabs i128-icmp i128-ineg i128-ireduce i128-load-store
i128-min-max i128-rotate i128-shifts i128-srem i128-urem iabs iaddcarry icmp-eq-imm icmp-eq
icmp-ne icmp-of-icmp icmp-sge icmp-sgt icmp-sle icmp-slt icmp-uge icmp-ugt icmp-ule icmp-ult
icmp ineg inline-probestack integer-minmax ireduce issue-14293 issue-5498 issue-6582 issue-6640
issue5497 issue5523 issue5524 issue5525 issue5526 issue5839 issue5884 issue5901 isubborrow
long-jump mul_overflow_flag_consumers or-and-y-with-not-y popcnt riscv64_issue_4996 rotl rotr
s390x-lxa sadd_overflow sdiv-i128 sdiv selectif-spectre-guard shift-right-left shifts
smul_overflow smulhi-aarch64 smulhi spill-reload srem srem_opts ssub_overflow stack-32
stack-addr-32 stack-addr-64 stack uadd_overflow uadd_overflow_128 uadd_overflow_narrow
uadd_overflow_trap udiv umul_overflow umulhi urem usub_overflow x64-bmi1 x64-bmi2"

VERBOSE=()
COMPARE=0
FILES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -v) VERBOSE=(-v) ;;
    --compare) COMPARE=1 ;;
    --all) FILES=("$RUNTESTS"/*.clif) ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) FILES+=("$1") ;;
  esac
  shift
done
if [[ ${#FILES[@]} -eq 0 ]]; then
  for f in $SUPPORTED; do FILES+=("$RUNTESTS/$f.clif"); done
fi

PKGS=(-p clif-native -p clif-runlines)
[[ $COMPARE -eq 1 ]] && PKGS+=(-p clif-oracle)
cargo build --quiet --release --manifest-path rust/Cargo.toml "${PKGS[@]}"
BIN=rust/target/release

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/native" "$WORK/oracle"

# One file per job; a nonzero exit (e.g. a missing tool) aborts the run.
run_one() {
  local f=$1 b
  b=$(basename "$f")
  "$BIN/clif-native" "$f" > "$WORK/native/$b.json" || [[ $? -eq 1 ]]
  if [[ $COMPARE -eq 1 ]]; then
    "$BIN/clif-oracle" interp "$f" > "$WORK/oracle/$b.json" || [[ $? -eq 1 ]]
  fi
}
export -f run_one
export BIN WORK COMPARE
printf '%s\0' "${FILES[@]}" | xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one "$1"' _

status=0
echo "== Native (aarch64, qemu) vs expectations"
native_json=()
for f in "${FILES[@]}"; do native_json+=("$WORK/native/$(basename "$f").json"); done
"$BIN/clif-results" summary "${VERBOSE[@]}" "${native_json[@]}" > "$WORK/summary.txt" || status=1
if [[ ${#VERBOSE[@]} -gt 0 ]]; then sed "s|$WORK/native/||" "$WORK/summary.txt"; else
  grep -v ': pass [0-9]* fail 0 print [0-9]* error 0 not-compiled 0 file-error 0$' "$WORK/summary.txt" |
    sed "s|$WORK/native/||" || true
fi

if [[ $COMPARE -eq 1 ]]; then
  echo "== Native vs the Cranelift interpreter (clif-oracle)"
  "$BIN/clif-results" compare "${VERBOSE[@]}" "$WORK/native" "$WORK/oracle" | sed "s|$WORK/||" || status=1
fi
exit $status

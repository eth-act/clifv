#!/usr/bin/env bash
# Random CLIF differential testing of Clif.run (T5, #41): generate runtest files with
# `clif-fuzz gen` (every subset-E opcode at i8..i64, every float operation at f32/f64, mixed
# functions; expectations = Clif.run), check them with Cranelift's reader + verifier
# (clif-oracle check), run them in the Cranelift interpreter (clif-oracle interp) and natively
# on aarch64 under qemu (clif-native), and compare every run with Clif.run (`clif-fuzz compare`:
# interpreter up to NaN payloads, native bit-exact).
#
# usage: scripts/clif-fuzz.sh [--seed S] [--per K] [--runs M] [--mix N] [--keep DIR]
#                             [--no-native] [--coverage] [-v]
#   --coverage: also print the static coverage of the existing runtests (interpreter-checked:
#   every runtests file + FVTest/Clif/fixtures; native-checked: the default file list of
#   scripts/aarch64-native-filetests.sh) over the keys of the generated files.
#
# Exit status 0 iff every generated file passes the verifier, no generated run is dropped
# (stuck), and no run disagrees (interpreter or native). Per-key counts: DIR/report.tsv.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

SEED=1; PER=2; RUNS=8; MIX=40; KEEP=""; NATIVE=1; COVERAGE=0; VERBOSE=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --seed) SEED=$2; shift ;;
    --per) PER=$2; shift ;;
    --runs) RUNS=$2; shift ;;
    --mix) MIX=$2; shift ;;
    --keep) KEEP=$2; shift ;;
    --no-native) NATIVE=0 ;;
    --coverage) COVERAGE=1 ;;
    -v) VERBOSE=(-v) ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
  shift
done

cargo build --quiet --release --manifest-path rust/Cargo.toml -p clif-oracle -p clif-native
lake build clif-fuzz 2>&1 | tail -1
BIN=rust/target/release
FUZZ=.lake/build/bin/clif-fuzz

if [[ -n $KEEP ]]; then W=$KEEP; rm -rf "$W"; mkdir -p "$W"; else W=$(mktemp -d); trap 'rm -rf "$W"' EXIT; fi
mkdir -p "$W/gen" "$W/interp" "$W/native" "$W/check"

status=0
echo "== Generate (seed $SEED)"
"$FUZZ" gen --seed "$SEED" --per "$PER" --runs "$RUNS" --mix "$MIX" --out-dir "$W/gen" || status=1

run_one() {
  local f=$1 b
  b=$(basename "$f")
  "$BIN/clif-oracle" check "$f" > "$W/check/$b.txt" 2>&1 || echo "$b" >> "$W/check/REJECTED"
  "$BIN/clif-oracle" interp "$f" > "$W/interp/$b.json" || true
  if [[ $NATIVE -eq 1 ]]; then
    "$BIN/clif-native" "$f" --timeout 600 > "$W/native/$b.json" || [[ $? -eq 1 ]]
  fi
}
export -f run_one
export BIN W NATIVE
printf '%s\0' "$W"/gen/*.clif | xargs -0 -n1 -P "$(nproc)" bash -c 'set -e; run_one "$1"' _

echo "== Cranelift reader + verifier"
if [[ -s $W/check/REJECTED ]]; then
  status=1
  while read -r b; do echo "rejected: $b"; head -20 "$W/check/$b.txt"; done < "$W/check/REJECTED"
fi
echo "generated files: $(ls "$W"/gen/*.clif | wc -l), rejected by cranelift: $(cat "$W/check/REJECTED" 2>/dev/null | wc -l)"

echo "== Clif.run vs the Cranelift interpreter and vs native aarch64"
NDIR=()
[[ $NATIVE -eq 1 ]] && NDIR=(--native-dir "$W/native")
"$FUZZ" compare "${VERBOSE[@]}" --interp-dir "$W/interp" "${NDIR[@]}" --report "$W/report.tsv" \
  "$W"/gen/*.clif || status=1

if [[ $COVERAGE -eq 1 ]]; then
  echo "== Coverage of the existing runtests (static, functions with run lines)"
  scripts/aarch64-native-filetests.sh --list > "$W/native-list.txt"
  "$FUZZ" coverage --universe "$W/gen" --native-list "$W/native-list.txt" \
    third_party/wasmtime/cranelift/filetests/filetests/runtests/*.clif FVTest/Clif/fixtures/*.clif \
    > "$W/coverage.tsv"
  tail -1 "$W/coverage.tsv"
  # before (static runtest coverage) → after (this run's agreeing runs), per key
  python3 - "$W/coverage.tsv" "$W/report.tsv" > "$W/before-after.tsv" <<'EOF'
import sys
cov = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open(sys.argv[1]) if '\t' in l and not l.startswith('key')}
rep = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open(sys.argv[2]) if not l.startswith('key')}
print('key\tE\tbefore_interp_files\tbefore_native_files\tafter_runs\tafter_interp_agree\tafter_native_agree')
tot = {}
for k in sorted(cov):
    e, bi, bn = cov[k][1], int(cov[k][2]), int(cov[k][3])
    r = rep.get(k)
    runs, ia, na = (int(r[2]), int(r[3]) + int(r[4]) + int(r[5]), int(r[8])) if r else (0, 0, 0)
    print(f'{k}\t{e}\t{bi}\t{bn}\t{runs}\t{ia}\t{na}')
    for grp in ('all', 'E' if e == 'E' else 'float/other'):
        t = tot.setdefault(grp, [0, 0, 0, 0, 0])
        t[0] += 1; t[1] += bi > 0; t[2] += bn > 0; t[3] += ia > 0; t[4] += na > 0
for g, t in tot.items():
    print(f'# {g}: keys {t[0]}; before: interpreter-checked {t[1]}, native-checked {t[2]}; after: interpreter-agreeing {t[3]}, native-agreeing {t[4]}', file=sys.stderr)
EOF
fi
[[ -n $KEEP ]] && echo "kept: $W (report.tsv, coverage.tsv, before-after.tsv)"
exit $status

#!/usr/bin/env bash
# Four-way differential testing of the DSL -> CLIF emitter (PLAN.md M1 exit criterion):
#
#   (a) denote          `lake exe compile-diff`: denote = expected = Clif.run (compile f) with the
#                       Lean map model, per test vector; onlySubsetE on every program
#   (b) Clif.run        `clif-filetest` on the emitted corpus/clif/*.clif (CLIF map runtime)
#   (c) interpreter     `clif-oracle interp` (Cranelift 0.136.1 interpreter)
#   (d) native aarch64  `clif-native` under qemu (CLIF map runtime), and again on
#                       corpus/clif/extrt/*.clif linked with the Rust `flat-runtime`
#
# The `; run:` expectations are denote's results encoded per the ABI (emitted by
# `lake exe emit`), so an engine "passes" a run line iff it agrees with denote; (c) and (d)
# are also compared record by record, and (b) with (c).
#
# usage: scripts/diff-corpus.sh [-v]
# Exit status 0 iff every engine agrees on every run line and every file passes
# `clif-oracle check`.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

VERBOSE=()
if [[ "${1:-}" == "-v" ]]; then VERBOSE=(-v); shift; fi

OUT=corpus/clif
BIN=rust/target/release
RTLIB=rust/target/aarch64-unknown-linux-musl/release/libflat_runtime.a

echo "== build"
lake build emit compile-diff clif-filetest 2>&1 | tail -1
cargo build --quiet --release --manifest-path rust/Cargo.toml \
  -p clif-oracle -p clif-native -p clif-runlines
cargo rustc --quiet --release --manifest-path rust/Cargo.toml -p flat-runtime \
  --target aarch64-unknown-linux-musl --crate-type staticlib -- -C panic=abort

echo "== emit"
rm -f "$OUT"/*.clif "$OUT"/extrt/*.clif
.lake/build/bin/emit "$OUT"

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/interp" "$WORK/native" "$WORK/native-rt" "$WORK/interp-rt"

status=0

echo "== (a) denote vs Clif.run (compile f) with the Lean map model"
.lake/build/bin/compile-diff "${VERBOSE[@]}" | tee "$WORK/a.txt" | tail -2 || status=1
grep -q "^FAIL" "$WORK/a.txt" && status=1

echo "== cranelift-reader + verifier (clif-oracle check)"
checked=0; rejected=0
for f in "$OUT"/*.clif "$OUT"/extrt/*.clif; do
  checked=$((checked + 1))
  if ! "$BIN/clif-oracle" check "$f" > "$WORK/check.txt" 2>&1; then
    rejected=$((rejected + 1)); status=1
    echo "rejected: $f"; cat "$WORK/check.txt"
  fi
done
echo "files: $checked, rejected: $rejected"

echo "== (c) Cranelift interpreter, (d) native aarch64"
for f in "$OUT"/*.clif; do
  b=$(basename "$f")
  "$BIN/clif-oracle" interp "$f" > "$WORK/interp/$b.json" || status=1
  "$BIN/clif-native" "$f" > "$WORK/native/$b.json" || status=1
done
for f in "$OUT"/extrt/*.clif; do
  b=$(basename "$f")
  "$BIN/clif-native" "$f" --link "$RTLIB" > "$WORK/native-rt/$b.json" || status=1
  cp "$WORK/interp/$b.json" "$WORK/interp-rt/$b.json"
done

echo "== (b) Clif.run vs expectations (= denote) and vs the interpreter"
.lake/build/bin/clif-filetest "${VERBOSE[@]}" --oracle-dir "$WORK/interp" "$OUT"/*.clif \
  > "$WORK/b.txt" || status=1
[[ ${#VERBOSE[@]} -gt 0 ]] && cat "$WORK/b.txt"
b_total=$(tail -1 "$WORK/b.txt")

summary() { "$BIN/clif-results" summary "${VERBOSE[@]}" "$@" | tail -1; }
compare() { "$BIN/clif-results" compare "${VERBOSE[@]}" "$1" "$2" | tail -1; }
c_total=$(summary "$WORK"/interp/*.json) || status=1
d_total=$(summary "$WORK"/native/*.json) || status=1
dr_total=$(summary "$WORK"/native-rt/*.json) || status=1
cd_total=$(compare "$WORK/interp" "$WORK/native") || status=1
cdr_total=$(compare "$WORK/interp-rt" "$WORK/native-rt") || status=1

echo
echo "== results"
echo "(a) denote / Clif.run+model:  $(tail -1 "$WORK/a.txt")"
echo "    $(tail -2 "$WORK/a.txt" | head -1)"
echo "(b) Clif.run:                 $b_total"
echo "(c) interpreter:              $c_total"
echo "(d) native (CLIF runtime):    $d_total"
echo "(d) native (Rust runtime):    $dr_total"
echo "(c) vs (d) CLIF runtime:      $cd_total"
echo "(c) vs (d) Rust runtime:      $cdr_total"

# Every run line must pass in every engine, and the pairwise comparisons must be clean.
for line in "$b_total"; do
  [[ "$line" =~ fail\ 0\ unsupported\ 0 && "$line" =~ disagree\ 0 && "$line" =~ oracle-error\ 0 ]] || status=1
done
for line in "$c_total" "$d_total" "$dr_total"; do
  [[ "$line" =~ fail\ 0\ print\ 0\ error\ 0\ not-compiled\ 0\ file-error\ 0 ]] || status=1
done
for line in "$cd_total" "$cdr_total"; do
  [[ "$line" =~ disagree\ 0\ error\ 0\ unmatched\ 0 ]] || status=1
done

if [[ $status -eq 0 ]]; then echo "ALL ENGINES AGREE"; else echo "DISAGREEMENT OR FAILURE"; fi
exit $status

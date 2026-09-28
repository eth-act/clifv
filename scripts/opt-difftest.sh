#!/usr/bin/env bash
# Differential tests of the Lean mid-end (FV/Opt, docs/contracts/midend.md).
#
# usage: scripts/opt-difftest.sh [-v] [--opt-* options] [--corpus] [--runtests] [--survey]
#                                [FILE.clif...]
#   default sets: --corpus --runtests --survey
#   --corpus:   corpus/clif/*.clif and corpus/clif/extrt/*.clif
#   --runtests: Cranelift's runtests/*.clif
#   --survey:   cg_clif survey output (scripts/rust-clif, $SURVEY, default /tmp/rust-clif-survey):
#               the smoke file with run lines (smoke/smoke.clif) and every tools/*.unopt.reader.clif
#               (no run lines: optimised and verifier-checked only); skipped if absent
#   --opt-*:    mid-end options (FVTest/Opt/Common.lean), passed to clif-opt and opt-difftest
#
# Per set:
# 1. `opt-difftest`: every `; run:` line through `Clif.run` before and after `Opt.optimize`;
#    returns and traps must agree (stuck/out-of-fuel source runs carry no obligation), and no
#    pass may produce an ill-formed function.
# 2. `clif-opt` writes the optimised file; `clif-oracle check` (cranelift-reader + verifier)
#    must accept it.
# 3. corpus and runtests: `clif-filetest` on the optimised files, with the Cranelift
#    interpreter (`clif-oracle interp`) run on the *optimised* files as oracle, and the same on
#    the original files: no file's summary may get worse (same pass/fail counts against the run
#    lines under Clif.run, no new disagreement with the interpreter), i.e. the optimised code
#    meets the expectations under both semantics wherever the original does.
# Exit status 0 iff every step passes.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
RUNTESTS=third_party/wasmtime/cranelift/filetests/filetests/runtests
SURVEY=${SURVEY:-/tmp/rust-clif-survey}

VERBOSE=()
OPTARGS=()
SETS=()
FILES=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -v) VERBOSE=(-v) ;;
    --opt-rules|--opt-rounds) OPTARGS+=("$1" "$2"); shift ;;
    --opt-*) OPTARGS+=("$1") ;;
    --corpus) SETS+=(corpus) ;;
    --runtests) SETS+=(runtests) ;;
    --survey) SETS+=(survey) ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) FILES+=("$1") ;;
  esac
  shift
done
if [[ ${#FILES[@]} -gt 0 ]]; then SETS+=(files); fi
if [[ ${#SETS[@]} -eq 0 ]]; then SETS=(corpus runtests survey); fi

lake build clif-opt opt-difftest clif-filetest 2>&1 | tail -1
cargo build --quiet --release --manifest-path rust/Cargo.toml -p clif-oracle
ORACLE=rust/target/release/clif-oracle

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
status=0

run_set() {
  local set=$1; shift
  local runfiles=() allfiles=()
  case "$set" in
    corpus) runfiles=(corpus/clif/*.clif corpus/clif/extrt/*.clif); allfiles=("${runfiles[@]}") ;;
    runtests) runfiles=("$RUNTESTS"/*.clif); allfiles=("${runfiles[@]}") ;;
    survey)
      if [[ ! -d "$SURVEY/tools" ]]; then echo "== survey: $SURVEY/tools not found, skipped"; return; fi
      [[ -f "$SURVEY/smoke/smoke.clif" ]] && runfiles=("$SURVEY/smoke/smoke.clif")
      allfiles=("${runfiles[@]}" "$SURVEY"/tools/*.unopt.reader.clif) ;;
    files) runfiles=("${FILES[@]}"); allfiles=("${FILES[@]}") ;;
  esac
  echo "== $set: Clif.run before vs after Opt.optimize"
  if [[ ${#runfiles[@]} -gt 0 ]]; then
    .lake/build/bin/opt-difftest "${VERBOSE[@]}" "${OPTARGS[@]}" "${runfiles[@]}" || status=1
  fi
  echo "== $set: clif-opt output through clif-oracle check (cranelift-reader + verifier)"
  mkdir -p "$WORK/$set"
  local i=0 checked=0 rejected=0
  for f in "${allfiles[@]}"; do
    i=$((i + 1))
    local out="$WORK/$set/$i-$(basename "$f")"
    .lake/build/bin/clif-opt "${OPTARGS[@]}" "$f" "$out" 2>/dev/null
    grep -q '^function' "$out" || continue
    checked=$((checked + 1))
    if ! "$ORACLE" check "$out" > "$WORK/check.txt" 2>&1; then
      rejected=$((rejected + 1)); status=1
      echo "REJECTED $f:"; head -20 "$WORK/check.txt"
    fi
  done
  echo "files checked $checked, rejected $rejected"
  if [[ "$set" == corpus || "$set" == runtests ]]; then
    echo "== $set: optimised vs original files: run expectations under Clif.run and the Cranelift interpreter"
    mkdir -p "$WORK/$set-orig" "$WORK/$set-oracle" "$WORK/$set-orig-oracle"
    i=0
    for f in "${allfiles[@]}"; do
      i=$((i + 1))
      cp "$f" "$WORK/$set-orig/$i-$(basename "$f")"
    done
    for d in "$set" "$set-orig"; do
      for out in "$WORK/$d"/*.clif; do
        "$ORACLE" interp "$out" > "$WORK/$d-oracle/$(basename "$out").json" 2>/dev/null || true
      done
    done
    .lake/build/bin/clif-filetest --oracle-dir "$WORK/$set-oracle" "$WORK/$set"/*.clif \
      > "$WORK/$set-opt.txt" || true
    .lake/build/bin/clif-filetest --oracle-dir "$WORK/$set-orig-oracle" "$WORK/$set-orig"/*.clif \
      > "$WORK/$set-orig.txt" || true
    # per-file summaries must not get worse (the originals' failures/disagreements are known
    # baseline issues of the tests or of the interpreter); `unsupported` counts differ because
    # clif-opt only prints the functions Clif.parseFile supports
    python3 - "$WORK/$set-orig.txt" "$WORK/$set-opt.txt" <<'PY' || status=1
import re, sys
def summ(p):
    d = {}
    for line in open(p):
        m = re.match(r"^\S*/(\d+-[^/:]+\.clif): (pass .*)$", line)
        # functions clif-opt drops (unsupported by Clif.parseFile) are not compared
        if m: d[m.group(1)] = re.sub(r" unsupported \d+", "", m.group(2))
    return d
a, b = summ(sys.argv[1]), summ(sys.argv[2])
def nums(s):
    return dict(re.findall(r"([a-z-]+) (\d+)", s or ""))
def worse(x, y):
    # same pass/fail counts and no new disagreement with the interpreter (the optimised code can
    # agree more often: constant folding avoids known interpreter deviations)
    x, y = nums(x), nums(y)
    return (x.get("pass") != y.get("pass") or x.get("fail") != y.get("fail")
            or int(y.get("disagree", 0)) > int(x.get("disagree", 0))
            or int(y.get("oracle-error", 0)) > int(x.get("oracle-error", 0)))
diff = [k for k in sorted(a) if worse(a.get(k), b.get(k))]
for k in diff: print(f"DIFFERENT {k}: original {a.get(k)} | optimised {b.get(k)}")
for k in sorted(a):
    if k not in diff and a.get(k) != b.get(k): print(f"improved {k}: original {a.get(k)} | optimised {b.get(k)}")
tot = [l for l in open(sys.argv[2]) if l.startswith("TOTAL")]
print(f"files {len(a)}, summaries not worse {len(a) - len(diff)}, worse {len(diff)}")
if tot: print("optimised " + tot[-1].strip())
sys.exit(1 if diff else 0)
PY
  fi
}

for set in "${SETS[@]}"; do run_set "$set"; done
exit $status

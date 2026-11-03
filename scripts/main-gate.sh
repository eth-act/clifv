#!/usr/bin/env bash
# Continuous main gate (docs/TO-PROVE.md §7, "Gate policy"): the full gate list on origin/main.
#
#   scripts/main-gate.sh run LOGDIR [CLIF [DEPS]]
#                                            the full list on this worktree's checkout (CLIF=1, the
#                                            default, includes clif-filetests and opt-difftest;
#                                            DEPS=1, the default, the examples/deps line);
#                                            takes /tmp/clifv-heavy.lock; exit 0 iff green,
#                                            3 when a host tool is missing (nothing run)
#   scripts/main-gate.sh loop WORKTREE       forever: check out the newest origin/main tip in
#                                            WORKTREE (a dedicated worktree), `run` it, record and
#                                            post the result on #261; stop: touch $GATE_DIR/stop
#                                            (takes effect between runs; killing the loop kills
#                                            its current run). A run that gets the lock after
#                                            origin/main moved on, or after a stop, is dropped.
#   scripts/main-gate.sh watch               block until the loop records a result or dies
#
# State (outside /tmp, survives reboots): GATE_DIR (default /home/kev/work/clifv-main-gate):
# results.tsv (sha, GREEN|RED, logdir, clif|-), runs/<sha8>/ (summary.log and every gate's log),
# loop.log, loop.pid. `loop` runs a copy of this script ($GATE_DIR/main-gate.sh), so checking out
# other commits does not change the running loop (restart the loop to pick up a new version).
#
# The list: lake-serial-build.py FV FVTest Corpus, then `lake build` of every library and
# executable; crate-proofs `lake build`; scripts/axiom-audit.py (scripts/audit/); lean-e2e-check;
# lean-backend-encode-check.sh; lean-backend-filetests.sh; arm-fault-cosim.sh; clif-filetests.sh against
# scripts/clif-filetests-baseline.txt and opt-difftest.sh (skipped by `loop` when no CLIF path
# changed since the last green run that ran them); cargo-fv and the Rust tools; examples/compare.sh
# --lean-link --verified on examples/fv-demo and examples/survey, and on examples/deps (its own
# gate line; skipped by `loop` when no DEPSPATHS path changed since the last green run: #691,
# #734) (cargo fv's per-executable binary check runs `cargo fv link-proof` + `lake exe
# link-check` on every test executable), and plain examples/compare.sh on
# examples/bigframe-unwind (#479: unwinding through a > 32 KiB Lean frame).
#
# Shared Lake cache: FV_LAKE_CACHE when set (it is in orb login shells), else
# /home/kev/work/clifv-lake-cache.
#
# Budgets (128 GB machine, docs/TO-PROVE.md §7): scheduler GATE_BUDGET (32G), module caps up to
# GATE_MAX_CAP (28G), single memcapped commands GATE_CAP (28G).
#
# The run-time gates call `qemu-aarch64-static`. When it is not on PATH (Ubuntu 26.04 has no
# qemu-user-static package; qemu-user's binaries are static but named qemu-aarch64), GATE_TOOLS
# (default /home/kev/work/clifv-tools/bin) goes first on PATH; set it up without root with
#   apt-get download qemu-user && dpkg-deb -x qemu-user_*.deb ../root  (in clifv-tools/deb)
#   ln -s ../root/usr/bin/qemu-aarch64 clifv-tools/bin/qemu-aarch64-static
set -u
command -v qemu-aarch64-static > /dev/null || export PATH="${GATE_TOOLS:-/home/kev/work/clifv-tools/bin}:$PATH"
GATE_DIR=${GATE_DIR:-/home/kev/work/clifv-main-gate}
LOCK=/tmp/clifv-heavy.lock
ISSUE=261
REPO=eth-act/clifv
CLIFPATHS='FV/Clif FV/Opt FV/Float FVTest/Clif FVTest/Opt scripts/clif-filetests.sh scripts/clif-filetests-baseline.txt scripts/opt-difftest.sh rust/crates/clif-oracle'
# the paths whose changes rerun the examples/deps line (lean-link's routes and the Stock
# production lowering it must reproduce, cargo-fv, the example itself)
DEPSPATHS='FV/Link FVTest/Link :(glob)FV/Backend/*Production*.lean rust/crates/cargo-fv examples/deps'

usage() { sed -n '2,16p' "$0" >&2; exit 2; }

# Host tools the gates need (docs/USAGE.md, "Install"): a missing one stops the gate with exit
# status 3 and is never recorded as a red run.
check_tools() {
  local t miss=()
  for t in qemu-aarch64-static clang python3 gh "${LLVM_MC:-/usr/lib/llvm-18/bin/llvm-mc}"; do
    command -v "$t" > /dev/null || miss+=("$t")
  done
  [ ${#miss[@]} = 0 ] || { echo "main-gate: missing host tools: ${miss[*]} (docs/USAGE.md, \"Install\")" >&2; return 3; }
}

run_gate() { # LOGDIR CLIF DEPS; cwd: the worktree root
  local L=$1 CLIF=${2:-1} DEPS=${3:-1} W fail=0 r
  W=$(pwd)
  mkdir -p "$L"
  export FV_LAKE_CACHE=${FV_LAKE_CACHE:-/home/kev/work/clifv-lake-cache}
  local cap=${GATE_CAP:-28G}
  local MC=(env FV_MEMCAP="$cap" LEAN_NUM_THREADS=2 scripts/memcap.sh)
  local M12=(env FV_MEMCAP=12G LEAN_NUM_THREADS=2 scripts/memcap.sh)
  {
  echo "start $(date -Is) HEAD $(git rev-parse --short=8 HEAD)"
  python3 scripts/lake-serial-build.py --budget "${GATE_BUDGET:-32G}" --max-cap "${GATE_MAX_CAP:-28G}" \
    --max-jobs 12 --others-by-usage --retry-failed --out "$L/sched" FV FVTest Corpus > "$L/sched.out" 2>&1
  r=$?; local nf; nf=$(grep -cE -- '-> fail' "$L/sched/sched.log" 2>/dev/null)
  echo "serial-build rc=$r fails=$nf: $(tail -n 1 "$L/sched/sched.log" 2>/dev/null)"
  [ "$r" = 0 ] && [ "$nf" = 0 ] || fail=1
  local EXES
  EXES=$(awk '/^\[\[/{sec=$0} sec=="[[lean_exe]]" && /^name *=/{gsub(/.*= *"|".*/,""); print}' lakefile.toml | tr '\n' ' ')
  echo "executables: $EXES"
  # shellcheck disable=SC2086
  "${MC[@]}" lake build FV FVTest Corpus $EXES > "$L/build.log" 2>&1
  r=$?; echo "full build rc=$r: $(tail -n 1 "$L/build.log")"; grep -E '^error|error:' "$L/build.log" | head -n 20; [ $r = 0 ] || fail=1
  (cd crate-proofs && env FV_MEMCAP="$cap" LEAN_NUM_THREADS=2 ../scripts/memcap.sh lake build) > "$L/crate.log" 2>&1
  r=$?; echo "crate-proofs rc=$r: $(tail -n 1 "$L/crate.log")"; [ $r = 0 ] || fail=1
  "${M12[@]}" python3 scripts/axiom-audit.py --log-dir "$L/audit" > "$L/axiom-audit.log" 2>&1; r=$?
  grep -E '^(ok|FAIL)|axiom audit' "$L/axiom-audit.log"; echo "axiom-audit rc=$r"; [ $r = 0 ] || fail=1
  "${M12[@]}" scripts/float-spec.sh > "$L/float-spec.log" 2>&1; r=$?
  grep -E '^(ok|FAIL)|axiom audit|build failed' "$L/float-spec.log"; echo "float-spec rc=$r"; [ $r = 0 ] || fail=1
  "${MC[@]}" lake exe lean-e2e-check > "$L/e2e.log" 2>&1; r=$?
  echo "lean-e2e-check rc=$r: $(grep -E 'accepted|rejected' "$L/e2e.log" | tail -n 3 | tr '\n' ' ')"; [ $r = 0 ] || fail=1
  "${MC[@]}" scripts/lean-backend-encode-check.sh > "$L/encoding.log" 2>&1; r=$?
  echo "encode-check rc=$r: $(grep -E 'functions [0-9]+:|differ' "$L/encoding.log" | tail -n 2 | tr '\n' ' ')"; [ $r = 0 ] || fail=1
  "${MC[@]}" scripts/lean-backend-filetests.sh > "$L/filetests.log" 2>&1; r=$?
  echo "filetests rc=$r: $(grep -E 'TOTAL|corpus|runtest' "$L/filetests.log" | tail -n 4 | tr '\n' ' ')"; [ $r = 0 ] || fail=1
  "${MC[@]}" scripts/arm-fault-cosim.sh > "$L/faultcosim.log" 2>&1; r=$?
  echo "arm-fault-cosim rc=$r: $(grep -E '^TOTAL' "$L/faultcosim.log" | tail -n 1)"; [ $r = 0 ] || fail=1
  if [ "$CLIF" = 1 ]; then
    "${MC[@]}" scripts/clif-filetests.sh > "$L/clif.log" 2>&1; r=$?
    local cur cp cf cd_ bp bf bd
    cur=$(grep -E 'TOTAL files [0-9]+: pass' "$L/clif.log" | tail -n 1)
    cp=$(echo "$cur" | grep -oE 'pass [0-9]+' | cut -d' ' -f2)
    cf=$(echo "$cur" | grep -oE 'fail [0-9]+' | head -n 1 | cut -d' ' -f2)
    cd_=$(echo "$cur" | grep -oE 'disagree [0-9]+' | cut -d' ' -f2)
    read -r bp bf bd < <(grep -v '^#' scripts/clif-filetests-baseline.txt | head -n 1)
    echo "clif-filetests rc=$r pass $cp fail $cf disagree $cd_ (baseline pass $bp fail $bf disagree $bd): $cur"
    if [ -n "$cp" ] && [ -n "$cf" ] && [ -n "$cd_" ] && [ "$cp" -ge "$bp" ] && [ "$cf" -le "$bf" ] && [ "$cd_" -le "$bd" ]; then :; else fail=1; fi
    "${MC[@]}" scripts/opt-difftest.sh > "$L/optdiff.log" 2>&1; r=$?
    echo "opt-difftest rc=$r: $(tail -n 3 "$L/optdiff.log" | tr '\n' ' ')"; [ $r = 0 ] || fail=1
  else
    echo "clif-filetests, opt-difftest: skipped (no CLIF path changed since the last green run with them)"
  fi
  (cd rust && FV_MEMCAP=12G ../scripts/memcap.sh cargo build --release -p cargo-fv -p clif-data-export -p lean-regalloc) > "$L/rust.log" 2>&1
  r=$?; echo "rust tools rc=$r"; [ $r = 0 ] || fail=1
  local CG=${FV_CG_CLIF:-$W/target/cg_clif/unwind/librustc_codegen_cranelift.so}
  if [ ! -f "$CG" ]; then
    FV_MEMCAP=12G scripts/memcap.sh scripts/build-cg-clif.sh > "$L/cg_clif.log" 2>&1 || echo "build-cg-clif rc=$?"
  fi
  for ex in fv-demo survey; do
    rm -rf "examples/$ex/target/fv"
    env PATH="$W/rust/target/release:$PATH" FV_ROOT="$W" FV_CG_CLIF="$CG" FV_MEMCAP=12G scripts/memcap.sh \
      examples/compare.sh "examples/$ex" --lean-link --verified > "$L/native_$ex.log" 2>&1
    r=$?; echo "cargo fv --lean-link --verified $ex rc=$r: $(grep -E '^SAME|DIFFERENT' "$L/native_$ex.log" | tr '\n' ' ')"
    { [ $r = 0 ] && grep -q '^SAME' "$L/native_$ex.log"; } || fail=1
  done
  # examples/deps (#691, #734): typed and Stock-lowered functions in one executable
  if [ "$DEPS" = 1 ]; then
    rm -rf "examples/deps/target/fv"
    env PATH="$W/rust/target/release:$PATH" FV_ROOT="$W" FV_CG_CLIF="$CG" FV_MEMCAP=12G scripts/memcap.sh \
      examples/compare.sh examples/deps --lean-link --verified > "$L/native_deps.log" 2>&1
    r=$?; echo "cargo fv --lean-link --verified deps rc=$r: $(grep -E '^SAME|DIFFERENT|binary check:' "$L/native_deps.log" | tr '\n' ' ')"
    { [ $r = 0 ] && grep -q '^SAME' "$L/native_deps.log"; } || fail=1
  else
    echo "cargo fv --lean-link --verified deps: skipped (no DEPSPATHS path changed since the last green run)"
  fi
  # #479: a panic unwinding through a Lean-compiled frame larger than 32 KiB (plain `cargo fv`:
  # the big function is outside the verified subset, so --verified would keep cg_clif's code)
  rm -rf examples/bigframe-unwind/target/fv
  env PATH="$W/rust/target/release:$PATH" FV_ROOT="$W" FV_CG_CLIF="$CG" FV_MEMCAP=12G scripts/memcap.sh \
    examples/compare.sh examples/bigframe-unwind > "$L/native_bigframe-unwind.log" 2>&1
  r=$?; echo "cargo fv bigframe-unwind rc=$r: $(grep -E '^SAME|DIFFERENT' "$L/native_bigframe-unwind.log" | tr '\n' ' ')"
  { [ $r = 0 ] && grep -q '^SAME' "$L/native_bigframe-unwind.log"; } || fail=1
  echo "end $(date -Is) RESULT=$([ $fail = 0 ] && echo GREEN || echo RED)"
  } > "$L/summary.log" 2>&1
  return $fail
}

post_result() { # SHA RESULT LOGDIR LASTGREEN
  local s res=$2 L=$3 lastgreen=$4
  s=$(git rev-parse --short=8 "$1")
  {
    echo "**Main gate $res** on \`$s\` ($(git log -1 --format=%s "$s" | cut -c1-100))"
    echo; echo '```'; cat "$L/summary.log"; echo '```'
    echo "Logs: \`$L\`"
    echo; echo "Last green commit: $([ -n "$lastgreen" ] && echo "\`$(git rev-parse --short=8 "$lastgreen")\`" || echo 'none yet')"
  } > "$L/comment.md"
  gh issue comment $ISSUE --repo $REPO --body-file "$L/comment.md" > /dev/null || echo "comment failed"
  if [ "$res" = GREEN ]; then
    gh api repos/$REPO/issues/$ISSUE --jq .body > "$L/issue_body.md" &&
    python3 - "$L/issue_body.md" "$s" "$(date -Is)" <<'EOF' &&
import re, sys
p, s, t = sys.argv[1:]
b = open(p).read()
b = re.sub(r"\*\*Last green commit:\*\*.*", lambda _: f"**Last green commit:** `{s}` ({t})", b)
open(p, "w").write(b)
EOF
    gh api -X PATCH repos/$REPO/issues/$ISSUE -F body=@"$L/issue_body.md" > /dev/null || echo "body update failed"
  fi
}

loop() { # WORKTREE
  local W=$1 R=$GATE_DIR/results.tsv
  touch "$R"; echo $$ > "$GATE_DIR/loop.pid"
  local run=
  # The run is its own process group (setsid); never leave it holding the lock when the loop dies.
  trap '[ -n "$run" ] && kill -TERM -- -"$run" 2>/dev/null; rm -f "$GATE_DIR/loop.pid"' EXIT
  trap 'exit 143' TERM INT HUP
  cd "$W" || exit 1
  while true; do
    [ -e "$GATE_DIR/stop" ] && { echo "stop $(date -Is)"; rm -f "$GATE_DIR/loop.pid"; exit 0; }
    git fetch -q origin || { sleep 300; continue; }
    local tip last lastgreen lastclif clif deps s L rc res
    tip=$(git rev-parse origin/main)
    last=$(awk -F'\t' 'END{print $1}' "$R")
    if [ "$tip" = "$last" ]; then sleep 600; continue; fi
    lastgreen=$(awk -F'\t' '$2=="GREEN"{g=$1} END{print g}' "$R")
    lastclif=$(awk -F'\t' '$4=="clif"{g=$1} END{print g}' "$R")
    clif=1
    # shellcheck disable=SC2086
    if [ -n "$lastclif" ] && git diff --quiet "$lastclif" "$tip" -- $CLIFPATHS; then clif=0; fi
    deps=1
    # shellcheck disable=SC2086
    if [ -n "$lastgreen" ] && git diff --quiet "$lastgreen" "$tip" -- $DEPSPATHS; then deps=0; fi
    git checkout -q --detach "$tip" || { echo "checkout of $tip failed"; sleep 600; continue; }
    s=$(git rev-parse --short=8 HEAD)
    L=$GATE_DIR/runs/$s
    echo "run $s start $(date -Is) clif=$clif deps=$deps"
    GATE_LOOP_TIP=$tip setsid flock "$LOCK" "$0" run-locked "$L" "$clif" "$deps" &
    run=$!
    wait "$run"; rc=$?; run=
    [ $rc = 4 ] && { echo "run $s dropped $(date -Is): origin/main moved on or stop requested while waiting for the lock"; continue; }
    [ $rc = 3 ] && { echo "run $s stopped $(date -Is): missing host tools, not recorded; loop exits"; rm -f "$GATE_DIR/loop.pid"; exit 3; }
    res=$([ $rc = 0 ] && echo GREEN || echo RED)
    [ $rc = 0 ] && lastgreen=$tip
    printf '%s\t%s\t%s\t%s\n' "$tip" "$res" "$L" "$([ $clif = 1 ] && [ $rc = 0 ] && echo clif || echo -)" >> "$R"
    echo "run $s end $(date -Is) $res"
    post_result "$tip" "$res" "$L" "$lastgreen"
  done
}

watch() {
  local R=$GATE_DIR/results.tsv n0 n pid
  n0=$(wc -l < "$R")
  pid=$(cat "$GATE_DIR/loop.pid" 2>/dev/null)
  while true; do
    n=$(wc -l < "$R")
    [ "$n" != "$n0" ] && { echo "MAIN-GATE:"; tail -n $((n - n0)) "$R"; exit 0; }
    { [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; } || { echo "LOOP-DIED"; tail -n 5 "$GATE_DIR/loop.log"; exit 0; }
    sleep 60
  done
}

mkdir -p "$GATE_DIR"
case "${1:-}" in
  run) [ $# -ge 2 ] || usage; flock "$LOCK" "$0" run-locked "$2" "${3:-1}" "${4:-1}" ;;
  run-locked)
    [ $# -ge 2 ] || usage; check_tools || exit 3; cd "$(git rev-parse --show-toplevel)" || exit 1
    if [ -n "${GATE_LOOP_TIP:-}" ]; then # started by `loop`: the lock wait may have been long
      [ -e "$GATE_DIR/stop" ] && exit 4
      git fetch -q origin && [ "$(git rev-parse origin/main)" != "$GATE_LOOP_TIP" ] && exit 4
    fi
    run_gate "$2" "${3:-1}" "${4:-1}" ;;
  loop)
    [ $# = 2 ] || usage
    W=$(cd "$2" && pwd) || exit 1
    if [ "$0" != "$GATE_DIR/main-gate.sh" ]; then
      cp "$0" "$GATE_DIR/main-gate.sh" && exec "$GATE_DIR/main-gate.sh" loop "$W"
    fi
    loop "$W" >> "$GATE_DIR/loop.log" 2>&1 ;;
  watch) watch ;;
  *) usage ;;
esac

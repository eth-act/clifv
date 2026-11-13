#!/usr/bin/env bash
# The Lean executables of the stock comparison (.github/workflows/stock-compiler-comparison.yml),
# without a cold build on one runner (#1018).
#
# Before this script the job has unstaged into the Lake cache (.github/actions/fv-lean) the Full
# gate build scripts/stock-comparison-lean-build.py chose and this workflow's own saved outputs.
# Lake restores from the cache every module whose inputs match; the others are built here by
# scripts/lake-serial-build.py with the limits the Full gate's shards use
# (.github/scripts/full-gate-shard.sh): heavy modules alone, light ones packed within the
# runner's memory, swap usable. A plain `lake build` starts one `lean` per core: that lost the
# runner at the same place twice and ran out of 60 minutes once (#1018).
#
# usage: .github/scripts/stock-comparison-lean.sh OUT STAGE
#   OUT    logs (the scheduler's in OUT/sched)
#   STAGE  `lake cache stage` directory of what is up to date at the end, for the workflow's
#          cache: all four executables after a complete build, otherwise the modules that built
#          (a re-run continues from them)
# STOCK_LEAN_LIMIT_S: seconds for the whole script (default 9000); when they are over, the
# script stops the build and fails. Appends to $GITHUB_OUTPUT `stage=full|partial|none` and
# `built=N` (modules built here). Every failure prints one `No stock-comparison result` error.
# Expects the Lake cache variables and FV_MEMCAP_OFF=1 (set by .github/actions/fv-lean).
set -euo pipefail
out=$1 stage=$2
limit=${STOCK_LEAN_LIMIT_S:-9000}
mkdir -p "$out"
rm -rf "$stage"
start=$(date +%s)
mapfile -t exes < <(python3 scripts/stock-comparison-lean-build.py --print exes)
mapfile -t roots < <(python3 scripts/stock-comparison-lean-build.py --print roots)
(( ${#exes[@]} && ${#exes[@]} == ${#roots[@]} )) || { echo "::error title=No stock-comparison result::the executable list is empty"; exit 1; }

# seconds left, at least 1 (`timeout 0` would mean no limit)
left() { local s=$(( limit - ($(date +%s) - start) )); echo $(( s > 0 ? s : 1 )); }
finish() {  # finish full|partial|none
  local built=0
  if [[ -f "$out/peaks.tsv" ]]; then built=$(grep -vc '^#' "$out/peaks.tsv" || true); fi
  if [[ -n ${GITHUB_OUTPUT:-} ]]; then printf 'stage=%s\nbuilt=%s\n' "$1" "$built" >> "$GITHUB_OUTPUT"; fi
  echo "Lean executables: $1 stage, $built module(s) built here, $(( $(date +%s) - start )) s"
}
no_result() {  # no_result MESSAGE: stage the modules that are up to date, then fail
  local kept=none
  # with out-of-date modules `lake build --no-build` exits non-zero but still lists the outputs
  # of every module that is up to date
  timeout --kill-after=30 600 lake build --no-build "${roots[@]}" -o "$out/partial-outputs.jsonl" \
    > "$out/partial-no-build.log" 2>&1 || true
  if [[ -s "$out/partial-outputs.jsonl" ]] && lake cache stage "$out/partial-outputs.jsonl" "$stage" > /dev/null 2>&1; then
    kept=partial
  fi
  finish "$kept"
  echo "::error title=No stock-comparison result::$1"
  exit 1
}

# The usual case: the chosen build is this commit's (or differs in no module of the executables).
if lake build --no-build "${exes[@]}" > "$out/restore.log" 2>&1; then
  echo "every module and executable restored: nothing to build"
else
  tail -n 5 "$out/restore.log"
  rc=0
  timeout --signal=TERM --kill-after=120 "$(left)" \
    python3 scripts/lake-serial-build.py --out "$out/sched" --record "$out/peaks.tsv" \
      --budget "${FV_CI_BUDGET:-15G}" --heavy "${FV_CI_HEAVY:-12G}" --heavy-avail 0 --pause-avail 1G \
      --max-jobs "${FV_CI_MAX_JOBS:-3}" --margin 1.0 --max-cap 48G --retry-failed --drift-time-scale 0 \
      "${roots[@]}" || rc=$?
  if (( rc == 124 || rc == 137 )); then
    no_result "the Lean build did not finish within $(( limit / 60 )) minutes. The modules that built are saved: re-run this job and it continues from them (or re-run once the Full gate has built this commit)."
  elif (( rc )); then
    grep -E ' (fail|blocked) \(' "$out/sched/sched.log" | tail -n 4 || true
    no_result "the Lean build failed (scheduler exit $rc): see the modules listed above and their logs in the artifact stock-comparison-artifacts (target/ci-lean/sched). A module that does not compile is this commit's error; a lost process is not: re-run this job."
  fi
  # the modules are built: compile their C and link (clang, light on memory)
  rc=0
  timeout --signal=TERM --kill-after=60 "$(left)" lake build "${exes[@]}" > "$out/link.log" 2>&1 || rc=$?
  tail -n 5 "$out/link.log"
  if (( rc == 124 || rc == 137 )); then
    no_result "linking the Lean executables did not finish within the $(( limit / 60 )) minutes of the Lean build. The modules are saved: re-run this job."
  elif (( rc )); then
    no_result "linking the Lean executables failed (lake exit $rc): see target/ci-lean/link.log in the artifact stock-comparison-artifacts."
  fi
fi

for exe in "${exes[@]}"; do
  test -x ".lake/build/bin/$exe" || no_result "lake reports $exe up to date but .lake/build/bin/$exe is missing."
done
if ! lake build --no-build "${exes[@]}" -o "$out/outputs.jsonl" > "$out/no-build.log" 2>&1; then
  tail -n 20 "$out/no-build.log"
  no_result "the Lean executables are out of date right after their build (see above)."
fi
lake cache stage "$out/outputs.jsonl" "$stage"
echo "stage: $(du -sh "$stage" | cut -f1), $(find "$stage" -type f | wc -l) files"
finish full

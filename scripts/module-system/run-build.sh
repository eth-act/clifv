#!/bin/bash
# usage: run-build.sh LABEL WORKTREE CACHE TARGETS...   (one measured scheduler run; never reruns)
label=$1 wt=$2 cache=$3; shift 3
out=/home/user/ms/runs/$label
if [ -e "$out/DONE" ]; then exec sleep infinity; fi
rm -rf "$out"; mkdir -p "$out"
cd "$wt" || exit 1
export FV_LAKE_CACHE=$cache
mkdir -p "$cache"
(while true; do echo "$(date +%s) $(awk '/MemTotal|MemAvailable/{printf "%s ", $2}' /proc/meminfo)"; sleep 5; done) > "$out/mem.log" &
mp=$!
git rev-parse HEAD > "$out/commit"; git status --short | wc -l > "$out/dirty"
s=$(date +%s.%N)
python3 scripts/lake-serial-build.py --out "$out/sched" --record "$out/peaks.tsv" \
  --profile /home/user/ms/profile-ci.tsv --profile "$wt/scripts/lake-module-peaks.tsv" \
  --budget 26G --max-jobs 8 --heavy 12G --heavy-avail 20G --pause-avail 3G --margin 1.0 \
  --min-cap 2G --max-cap 28G --retry-failed --no-dedup "$@" > "$out/build.log" 2>&1
rc=$?
e=$(date +%s.%N)
echo "rc=$rc wall_s=$(echo "$e - $s" | bc) targets=$*" > "$out/result"
if [ -n "${MS_EXE:-}" ]; then
  s=$(date +%s.%N)
  scripts/memcap.sh lake build $MS_EXE > "$out/exe.log" 2>&1; rc=$?
  e=$(date +%s.%N)
  echo "exe rc=$rc wall_s=$(echo "$e - $s" | bc) $MS_EXE" >> "$out/result"
fi
kill $mp
touch "$out/DONE"
exec sleep infinity

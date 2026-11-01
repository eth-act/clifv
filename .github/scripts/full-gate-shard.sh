#!/usr/bin/env bash
# One shard of the full-gate build (.github/workflows/full-gate.yml): build the modules
# scripts/ci-build-plan.py assigned to shard SHARD of wave WAVE, with the memory-aware scheduler,
# then stage their Lake cache outputs in OUT/stage for the later waves.
#
# usage: .github/scripts/full-gate-shard.sh PLAN.json WAVE SHARD OUT
# Expects the Lake cache variables (LAKE_ARTIFACT_CACHE, LAKE_RESTORE_ARTIFACTS, LAKE_CACHE_DIR)
# and FV_MEMCAP_OFF=1 (no cgroup scopes on runners; swap stays usable); the imports from earlier
# waves and the baseline build must already be unstaged into LAKE_CACHE_DIR.
set -euo pipefail
plan=$1 wave=$2 shard=$3 out=$4
mkdir -p "$out"
python3 - "$plan" "$wave" "$shard" > "$out/modules.txt" <<'EOF'
import json, sys
plan = json.load(open(sys.argv[1]))
print("\n".join(plan["waves"][int(sys.argv[2]) - 1][int(sys.argv[3])]["modules"]))
EOF
mapfile -t mods < "$out/modules.txt"
echo "wave $wave shard $shard: ${#mods[@]} modules"
# Default limits for a 16 GB GitHub-hosted runner with swap: light modules packed within 15G of
# recorded peaks (at most 3 lean processes on 4 vCPUs), modules above 12G alone; caps only steer
# the packing. A larger runner sets FV_CI_BUDGET / FV_CI_HEAVY / FV_CI_MAX_JOBS (repository
# variables FULL_GATE_BUDGET / FULL_GATE_HEAVY / FULL_GATE_MAX_JOBS, docs/TO-PROVE.md §7).
python3 scripts/lake-serial-build.py --only "$out/modules.txt" --out "$out/sched" \
  --record "$out/peaks.tsv" --budget "${FV_CI_BUDGET:-15G}" --heavy "${FV_CI_HEAVY:-12G}" \
  --heavy-avail 0 --pause-avail 1G --max-jobs "${FV_CI_MAX_JOBS:-3}" --margin 1.0 --max-cap 48G \
  --retry-failed --drift-time-scale 0 \
  "${mods[@]}"
lake build --no-build "${mods[@]}" -o "$out/outputs.jsonl"
lake cache stage "$out/outputs.jsonl" "$out/stage"
du -sh "$out/stage"

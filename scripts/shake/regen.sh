#!/usr/bin/env bash
# Regenerate the unused-import removal on the current checkout (scripts/shake/shake.py), e.g. on a
# fresh main right before merging: build everything, analyse, edit, build again.
#
# usage: scripts/shake/regen.sh [lake-serial-build.py options, e.g. --budget 48G]
#
# Needs FV_LAKE_CACHE (or a warm .lake) to be fast; the analysis loads the .olean files of FV,
# FVTest, Corpus and crate-proofs. Afterwards: `git diff --stat`, then the gates (PR body).
set -euo pipefail
cd "$(dirname "$0")/../.."
out=${SHAKE_OUT:-/tmp/shake-regen}
mkdir -p "$out"
scripts/lake-serial-build.py --out "$out/before" "$@" FV FVTest Corpus
# crate-proofs: analysed if built (cd crate-proofs && lake build), else the old closures of its imports are kept
python3 scripts/shake/shake.py --report "$out/report.json"
scripts/lake-serial-build.py --out "$out/after" "$@" FV FVTest Corpus

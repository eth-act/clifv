#!/usr/bin/env bash
# Build `clifv-extract-lean` (the extracted pipeline + driver) against the pinned Aeneas fork
# checked out and built by build-tools.sh ($WORK/tools/aeneas), reusing that checkout's Lean
# packages (Mathlib, ...) instead of fetching them again for extract/lean.
#
# The build directory $WORK/lean-build is a lake project whose sources are symlinks into
# extract/lean (Generated/, Models/, ClifvExtract/): the same modules as extract/lean/lakefile.lean,
# which pins the same Aeneas commit as a git dependency for standalone builds.
# Prints the path of the executable on the last line.
set -euo pipefail
EXTRACT=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(dirname "$EXTRACT")
WORK=${CLIFV_EXTRACT_WORK:-/data/clifv-extract}
AENEAS=$WORK/tools/aeneas
BUILD=$WORK/lean-build
export OMP_NUM_THREADS=2 OMP_THREAD_LIMIT=2 LEAN_NUM_THREADS=2
heavy() { flock "$WORK/heavy.lock" env FV_MEMCAP=64G bash "$ROOT/scripts/memcap.sh" nice -n 10 "$@"; }

pin=$(python3 -c "import json,sys; print(json.load(open('$EXTRACT/pins.json'))['aeneas']['commit'])")
[ "$(git -C "$AENEAS" rev-parse HEAD)" = "$pin" ] || {
  echo "$AENEAS is not at the pinned commit $pin (run build-tools.sh)" >&2; exit 1; }

mkdir -p "$BUILD/.lake"
cp "$EXTRACT/lean/lean-toolchain" "$BUILD/"
ln -sfn "$AENEAS/tests/lean/.lake/packages" "$BUILD/.lake/packages"
for d in Generated Models ClifvExtract; do ln -sfn "$EXTRACT/lean/$d" "$BUILD/$d"; done
# The lakefile of extract/lean, with the local Aeneas checkout instead of the git dependency.
sed -e "/^require aeneas from git/,+1c\\
require aeneas from \"$AENEAS/backends/lean\"" "$EXTRACT/lean/lakefile.lean" > "$BUILD/lakefile.lean"
# Same manifest as the Aeneas tests project (the Mathlib revision of the pinned Aeneas).
python3 - "$AENEAS/tests/lean/lake-manifest.json" "$BUILD/lake-manifest.json" "$AENEAS/backends/lean" <<'EOF'
import json, sys
m = json.load(open(sys.argv[1]))
m["name"] = "clifvExtract"
for p in m["packages"]:
    if p["name"] == "aeneas":
        p["dir"] = sys.argv[3]
json.dump(m, open(sys.argv[2], "w"), indent=1)
EOF
(cd "$BUILD" && heavy lake build clifv-extract-lean) >&2
echo "$BUILD/.lake/build/bin/clifv-extract-lean"

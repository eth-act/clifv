#!/usr/bin/env bash
# Build the pinned Charon/Aeneas forks (extract/pins.json) under $CLIFV_EXTRACT_WORK/tools.
# Idempotent: a checkout at the pinned commit with its bin/ artifacts present is not rebuilt.
# Heavy steps run under the resource rule (memcap 64G, nice, 2 jobs).
set -euo pipefail
EXTRACT=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(dirname "$EXTRACT")
WORK=${CLIFV_EXTRACT_WORK:-/data/clifv-extract}
TOOLS=$WORK/tools
mkdir -p "$TOOLS"
export OMP_NUM_THREADS=2 OMP_THREAD_LIMIT=2 LEAN_NUM_THREADS=2 CARGO_BUILD_JOBS=2
heavy() { FV_MEMCAP=64G bash "$ROOT/scripts/memcap.sh" nice -n 10 "$@"; }
pin() { python3 -c "import json,sys;print(json.load(open('$EXTRACT/pins.json'))['$1']['$2'])"; }

checkout() { # name -> prints 1 if the checkout moved
  local name=$1 repo commit dir moved=0
  repo=$(pin "$name" repo); commit=$(pin "$name" commit); dir=$TOOLS/$name
  [ -d "$dir/.git" ] || git clone -q "$repo" "$dir"
  if [ "$(git -C "$dir" rev-parse HEAD)" != "$commit" ]; then
    git -C "$dir" fetch -q origin
    git -C "$dir" checkout -q "$commit"
    moved=1
  fi
  echo "$moved"
}

charon_moved=$(checkout charon)
aeneas_moved=$(checkout aeneas)

# Charon (Rust, its own rust-toolchain via rustup; the OCaml side is built by Aeneas' dune).
if [ "$charon_moved" = 1 ] || [ ! -x "$TOOLS/charon/bin/charon" ] || [ ! -x "$TOOLS/charon/bin/charon-driver" ]; then
  (cd "$TOOLS/charon" && heavy make build-charon-rust)
fi

ln -sfn ../charon "$TOOLS/aeneas/charon"

# OCaml switch (5.3.0; falls back per extract/pins.json "ocaml" if recorded).
OCAML=$(python3 -c "import json;print(json.load(open('$EXTRACT/pins.json')).get('ocaml','5.3.0'))")
SWITCH=$TOOLS/opam
if [ ! -d "$SWITCH/_opam" ]; then
  opam switch create "$SWITCH" "$OCAML" --yes
fi
if [ ! -f "$SWITCH/.clifv-deps-installed" ] || [ "$aeneas_moved" = 1 ]; then
  (cd "$TOOLS/aeneas" && opam install --switch="$SWITCH" ./src --deps-only --yes -j 2)
  # charon-ml (built by Aeneas' dune through the `charon` symlink) also needs this one.
  opam install --switch="$SWITCH" "ppx_deriving_hash>=0.1.5" --yes -j 2
  touch "$SWITCH/.clifv-deps-installed"
fi

if [ "$aeneas_moved" = 1 ] || [ "$charon_moved" = 1 ] || [ ! -x "$TOOLS/aeneas/bin/aeneas" ]; then
  (cd "$TOOLS/aeneas" && heavy opam exec --switch="$SWITCH" -- make build-dev)
fi

# Lean backend library (Mathlib cache, then the Aeneas library).
if [ "$aeneas_moved" = 1 ] || [ ! -d "$TOOLS/aeneas/backends/lean/.lake/build/lib" ]; then
  (cd "$TOOLS/aeneas/backends/lean" && heavy lake exe cache get && heavy lake build)
fi
echo "tools ready: $TOOLS/charon/bin/charon $TOOLS/aeneas/bin/aeneas"

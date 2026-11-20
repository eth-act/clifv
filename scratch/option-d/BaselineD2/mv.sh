#!/usr/bin/env bash
# BaselineD2 (option D measurement, scratch): the mid-end validator (midval-check --cert, the three
# saved binaries: main 5e21e6bfe = before #1136, #1136 0a42dc718, #1138 d1fc25665) on the dump pairs
# of the 9 release crates generated with cg_clif on Cranelift 0.135.0 and on 0.136.1; analyze.py
# joins the verdicts with the release parity of the same Cranelift (projection).
set -uo pipefail
B=$HOME/clifv/tmp/BaselineD1
B2=$HOME/clifv/tmp/BaselineD2
mkdir -p "$B2"
for cl in ${CLS:-0.135.0 0.136.1}; do
  for b in ${BINS:-main 1136 1138}; do
    O=$B2/mv-$cl-$b
    rm -rf "$O"
    echo "== $cl $b"
    X=$B/bin/midval-check-$b P=${P:-16} bash "$B/run-check.sh" "$B/dumps-$cl" "$O"
    python3 "$B/analyze.py" "$O" "$B/rel-$cl" >"$B2/analysis-$cl-$b.txt"
    grep -E "^\| \*\*total|^projected|^unmatched" "$B2/analysis-$cl-$b.txt"
    if [[ $cl == 0.136.1 && -d $B2/relp-0.136.1 ]]; then
      python3 "$B/analyze.py" "$O" "$B2/relp-0.136.1" >"$B2/analysis-$cl-drop-$b.txt"
      grep -E "^\| \*\*total|^projected|^unmatched" "$B2/analysis-$cl-drop-$b.txt" | sed 's/^/  +drop: /'
    fi
  done
done

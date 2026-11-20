#!/usr/bin/env bash
# BaselineD3 (option D measurement, scratch): what BaselineD2's chain2.sh steps 5 and 6 left.
#   a deps (0.136.1, plain, wt BaselineD1): prototype off / on, --no-binary-check  -> BaselineD2/proto5off, proto5on
#   b std line `fv-demo --build-std`, gate mode (--lean-link --verified, binary check on), both
#     Cranelifts, wt BaselineD1-meas, ACT=cg_clif-active3                           -> BaselineD2/debug
#   c std line plain off / on with 0.136.1 (wt BaselineD1), --no-binary-check      -> BaselineD2/proto5off, proto5on
# Each step starts only while no clifv-MergeTrain* or *-gate unit is active.
set -uo pipefail
B2=$HOME/clifv/tmp/BaselineD2
D4=$HOME/clifv/tmp/BaselineD3/debug4.sh
M=$HOME/clifv/wt/BaselineD1-meas
P=$HOME/clifv/wt/BaselineD1
export LEAN_NUM_THREADS=16 FV_JOBS=16 CARGO_BUILD_JOBS=16
busy() { systemctl --user list-units --state=active --no-legend --plain 'clifv-*' | awk '{print $1}' | grep -qE '^clifv-MergeTrain|-gate(-[^.]*)?\.service$'; }
waitfree() { while busy; do sleep 120; done; echo "== free of train/gate units $(date -Is)"; }
has() { [[ " $STEPS " == *" $1 "* ]]; }
df -h / | tail -1
if has a; then waitfree; echo "== step a $(date -Is)"
  (cd "$P" && NOBC=1 FV_SCRATCH_NOTRAP_OFF=1 W=$P PLAIN=1 CLS=0.136.1 bash "$D4" "$B2/proto5off" deps)
  (cd "$P" && NOBC=1 W=$P PLAIN=1 CLS=0.136.1 REF=$B2/proto5off bash "$D4" "$B2/proto5on" deps); fi
if has b; then waitfree; echo "== step b $(date -Is)"
  (cd "$M" && W=$M ACT=$M/target/cg_clif-active3 bash "$D4" "$B2/debug" fv-demo+std); fi
if has c; then waitfree; echo "== step c $(date -Is)"
  (cd "$P" && NOBC=1 FV_SCRATCH_NOTRAP_OFF=1 W=$P PLAIN=1 CLS=0.136.1 bash "$D4" "$B2/proto5off" fv-demo+std)
  (cd "$P" && NOBC=1 W=$P PLAIN=1 CLS=0.136.1 REF=$B2/proto5off bash "$D4" "$B2/proto5on" fv-demo+std); fi
df -h / | tail -1
echo "== chain3 $STEPS done $(date -Is)"

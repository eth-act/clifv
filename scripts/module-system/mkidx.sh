#!/bin/bash
# mkidx.sh OUT : definition index of the lean-backend closure: port-mech build (all), then the
# repo's current build (modules with an .olean), later lines win in expose.py
T=~/.elan/toolchains/leanprover--lean4---v4.34.1
[ -s /home/user/ms/idx-mech.txt ] || (cd /home/user/workspace/port-mech && LEAN_PATH=.lake/build/lib/lean:$T/lib/lean lean --run /home/user/ms/declidx.lean $(cat /home/user/ms/lbmods.txt) > /home/user/ms/idx-mech.txt)
cd /home/user/workspace/repo
mods=$(for m in $(cat /home/user/ms/lbmods.txt) FV.SimprocAttr FV.Arm.Insts.CommonBits; do f=.lake/build/lib/lean/$(echo $m | tr . /).olean; [ -f $f ] && echo $m; done)
LEAN_PATH=.lake/build/lib/lean:$T/lib/lean lean --run /home/user/ms/declidx.lean $mods > /tmp/ms_idx_cur.txt 2>/tmp/ms_idx_cur.err
(sed "s/$/\tmech/" /home/user/ms/idx-mech.txt; sed "s/$/\tcur/" /tmp/ms_idx_cur.txt) > "$1"

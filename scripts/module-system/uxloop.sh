#!/bin/bash
# uxloop.sh MODULE : build; on failure autofix + expose (+closure); repeat while something changes
m=$1
for i in $(seq 20); do
  /home/user/ms/try.sh "$m" > /tmp/ms_ux_$m.out; head -3 /tmp/ms_ux_$m.out
  grep -q 'rc=0' /tmp/ms_ux_$m.out && exit 0
  cd /home/user/workspace/repo
  out=$(python3 /home/user/ms/autofix.py /tmp/ms_try_$m.log)
  [ -z "$out" ] && out=$(python3 /home/user/ms/expose.py /tmp/ms_idx_all.txt /tmp/ms_try_$m.log 2>/dev/null)
  [ -z "$out" ] && out=$(python3 /home/user/ms/expose.py --closure /tmp/ms_idx_all.txt /tmp/ms_try_$m.log 2>/dev/null)
  [ -z "$out" ] && out=$(python3 /home/user/ms/expose.py --files /tmp/ms_idx_all.txt /tmp/ms_try_$m.log 2>/dev/null)
  echo "$out" | tee -a /home/user/ms/runs/drv-ux/exposed-manual.tsv | head -5
  [ -z "$out" ] && exit 1
done

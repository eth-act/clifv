#!/bin/bash
# fixloop.sh MODULE : build, autofix, repeat while autofix changes something (max 15 rounds)
for i in $(seq 15); do
  /home/user/ms/try.sh "$1" > /tmp/ms_fl_$1.out; cat /tmp/ms_fl_$1.out | head -4
  grep -q 'rc=0' /tmp/ms_fl_$1.out && exit 0
  out=$(cd /home/user/workspace/repo && python3 /home/user/ms/autofix.py /tmp/ms_try_$1.log)
  echo "$out"
  [ -z "$out" ] && exit 1
done

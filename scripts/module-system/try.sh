#!/bin/bash
# try.sh MODULE... : lake build each (memcapped, own cache), print errors only
cd /home/user/workspace/repo; export FV_LAKE_CACHE=/home/user/ms/cache-port-dev
for m in "$@"; do
  FV_MEMCAP=${CAP:-14G} LEAN_NUM_THREADS=2 timeout ${TMO:-1800} scripts/memcap.sh lake build "$m" > /tmp/ms_try_$m.log 2>&1
  rc=$?
  if [ $rc -ne 0 ] && grep -q 'permission denied (error code: 13)' /tmp/ms_try_$m.log; then
    grep -A1 'permission denied (error code: 13)' /tmp/ms_try_$m.log | sed -n 's/^ *file: //p' | xargs -r rm -f
    FV_MEMCAP=${CAP:-14G} LEAN_NUM_THREADS=2 timeout ${TMO:-1800} scripts/memcap.sh lake build "$m" > /tmp/ms_try_$m.log 2>&1
    rc=$?
  fi
  echo "== $m rc=$rc"; grep -E '^error' /tmp/ms_try_$m.log | grep -v 'build failed' | head -${N:-6} | cut -c1-300
done

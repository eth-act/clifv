#!/bin/bash
# coreall.sh MODULE... : one line per module, `M: core modules to import all` (empty if none or not built)
T=~/.elan/toolchains/leanprover--lean4---v4.34.1
cd /home/user/workspace/base
for m in "$@"; do
  LEAN_PATH=${BASE_LIB:-/home/user/workspace/base/.lake/build/lib/lean:/home/user/ms/base-lb-lake/build/lib/lean}:$T/lib/lean \
    lean --run /home/user/ms/coreall.lean "$m" 2>/dev/null | grep "^$m:" || echo "$m: NOTBUILT"
done

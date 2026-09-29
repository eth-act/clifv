#!/usr/bin/env bash
# Build the freestanding Rust runtime for the rust-route smoke tests (step 2):
# `memcpy`/`memset`/`memmove`/`memcmp` plus every diverging `core` panic entry the
# corpus references (each aborts with `udf`, i.e. never returns).
#
#   scripts/rust-clif/rust-runtime.sh <out.o> [<out-panic-stubs>]
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=$1; shift || true
mkdir -p "$(dirname "$out")"
stub_s="${out%.o}_panic.s"
stub_o="${out%.o}_panic.o"

# the corpus's undefined symbols: every panic-ish one is a diverging entry point
survey="${RR_SURVEY:-/tmp/rust-clif-survey}"
undef=$(for c in a_arith b_slices c_structs_enums d_loops_iters e_option_result f_crypto \
        g_u128 h_dyn_generic i_alloc; do cat "$survey/out/debug/$c/$c.undef" 2>/dev/null; done | sort -u)
panics=$(echo "$undef" | grep -E "panic|fail|handle_alloc_error|handle_error|Formatter|3fmt" || true)

# 1. the mem* implementations (C)
clang --target=aarch64-linux-gnu -ffreestanding -fno-builtin -nostdlib -O1 \
  -c "$root/scripts/rust-clif/rust-runtime.c" -o "$out"

# 2. panic stubs: one symbol per entry, each jumping to the shared abort stub.
{
  echo ".section .text.rustroute_panic, \"ax\", @progbits"
  echo "rustroute_abort:"
  echo "    udf #251"
  for p in $panics; do
    echo ".globl $p"
    echo "$p:"
    echo "    b rustroute_abort"
  done
} > "$stub_s"
clang --target=aarch64-linux-gnu -c "$stub_s" -o "$stub_o"
echo "rust runtime: mem* + $(echo "$panics" | wc -l) panic stubs"

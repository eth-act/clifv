# Contract: Cranelift drivers (`clif2obj`, `clif-native`, `clif-results`)

Producer: M1/M3 driver work. Consumers: M1 differential testing (four-way: `denote`,
`Clif.run`, Cranelift interpreter, native), M3 validator (per-function dumps), M1 runtime
(linked into native tests with `--link`). Pinned against Cranelift 0.136.1 (`docs/PINS.md`).

## Status

- [x] `rust/crates/clif2obj` (lib + bin): PLAN.md Appendix A ported to 0.136.1, with
      relocation and trap dumps; Appendix B checked (below).
- [x] `rust/crates/clif-runlines` (lib + `clif-results` bin): run-command handling and the
      JSON schema shared by `clif-oracle` and `clif-native` (`clif-oracle` now uses it; its
      output is byte-identical to before on all 395 runtests, 13733 records).
- [x] `rust/crates/clif-native`: native execution of `; run` lines under qemu.
- [x] `scripts/aarch64-native-filetests.sh`: 128 supported runtest files, **4894 pass,
      0 fail, 0 error**, 578 not compiled by Cranelift's aarch64 backend (below).
- [x] `rust/crates/clif-native/tests/native.rs`: traps, multi-value returns, `--link`,
      unresolved externs, crash/hang recovery.

Commands:

```
cargo build --release --manifest-path rust/Cargo.toml -p clif2obj -p clif-native -p clif-runlines
rust/target/release/clif2obj [--colocated-externs] IN.clif aarch64-unknown-linux-gnu OUT.o DUMP_DIR
rust/target/release/clif-native FILE.clif [--link OBJ_OR_ARCHIVE]... [--keep DIR] [--timeout SECS]
rust/target/release/clif-results summary [-v] FILE.json...
rust/target/release/clif-results compare [-v] DIR_A DIR_B
scripts/aarch64-native-filetests.sh [-v] [--compare] [--all | FILE.clif...]
cargo test --manifest-path rust/Cargo.toml -p clif-native
```

## Code generation settings (both drivers, `clif2obj::SETTINGS`)

Exactly `opt_level=none`, `enable_verifier=true`, `regalloc_checker=true`, `is_pic=true`;
every other shared and ISA setting is Cranelift's default (no `has_lse`, etc.).
`test`/`target`/`set` header lines of the input are accepted and **ignored** for code
generation. Signatures without an explicit calling convention get the target's C calling
convention (`system_v` for `aarch64-unknown-linux-gnu`, PLAN.md §3.2), not the reader's
default `fast` (cranelift-reader itself uses the host's C convention when the file has a
`test run` line; on x86-64 Linux that is also `system_v`). Explicit conventions (`tail`,
`fast`, ...) are kept.

Symbols: function `%name` → exported symbol `name` (`Linkage::Export`). A declaration
`fnN = [colocated] %callee(sig)` refers to the file's function `callee` if there is one,
otherwise to an imported (undefined) symbol `callee`. Non-colocated calls go through the
GOT (`is_pic`), colocated ones are direct `bl`. Function names must be `%name`
(`u0:1`-style names are rejected); `gvN = symbol %x` data symbols are rejected.

## `clif2obj`

```
clif2obj [--colocated-externs] <input.clif> <target-triple> <out.o> <dump-dir>
```

Compiles every function of the file into one relocatable object `out.o` and writes, per
function `name`, into `dump-dir`:

| File | Content |
| --- | --- |
| `name.bin` | raw machine code of the function (the bytes placed in `.text`, incl. constant islands) |
| `name.clif` | the function as Cranelift parsed it (before lowering, before extern renaming; calling conventions resolved as above) |
| `name.vcode` | post-regalloc VCode listing (`Context::set_disasm`), with block labels and trap annotations |
| `name.relocs.json` | relocations, schema below |
| `name.traps.json` | trap sites, schema below |

`--colocated-externs` treats every `fnN` as `colocated` (direct `bl` + `Arm64Call`).
Exit status 0 on success; 1 with a message on stderr otherwise (reader error, verifier
error printed with the offending instruction, unsupported lowering).

`name.relocs.json` (array, in code order):

```json
[{"offset": 64, "kind": "Aarch64AdrGotPage21", "target": "balance_of", "addend": 0},
 {"offset": 68, "kind": "Aarch64Ld64GotLo12Nc", "target": "balance_of", "addend": 0}]
```

- `offset`: byte offset of the instruction from the function start.
- `kind`: Cranelift's `binemit::Reloc` variant name. On aarch64: `Aarch64AdrGotPage21` +
  `Aarch64Ld64GotLo12Nc` (GOT load of a callee address → `blr`: treat as an abstract call
  of `target`), `Arm64Call` (direct `bl`), and for other constructs e.g.
  `Aarch64AdrPrelPgHi21`/`Aarch64AddAbsLo12Nc`, `Abs8`.
- `target`: symbol name (a file function, an import, or a libcall name such as `memcpy`
  from `cranelift_module::default_libcall_names`). A reference to an offset inside the
  function itself uses the function's own symbol with the offset added to `addend`.
- `addend`: signed.

`name.traps.json` (array): `[{"offset": 108, "code": "int_ovf"}]` — byte offset of each
trapping instruction (the `udf`, or a load/store that may fault) and its CLIF trap code name
(`stk_ovf heap_oob int_ovf int_divz bad_toint userN`).

### Appendix B (adapted to 0.136.1: `iadd_imm` → `iconst` + `iadd`), observed

`clif2obj sum_balances.clif aarch64-unknown-linux-gnu out.o dump` then
`llvm-objdump -dr out.o`:

```
0000000000000000 <sum_balances>:
       0: a9bf7bfd      stp     x29, x30, [sp, #-0x10]!
       4: 910003fd      mov     x29, sp
       8: f81f0ff5      str     x21, [sp, #-0x10]!
       c: a9bf53f3      stp     x19, x20, [sp, #-0x10]!
      10: aa0003e2      mov     x2, x0
      14: d2800000      mov     x0, #0x0                // =0
      18: aa0003f5      mov     x21, x0
      1c: aa0103f3      mov     x19, x1
      20: b50000d3      cbnz    x19, 0x38 <sum_balances+0x38>
      24: aa1503e0      mov     x0, x21
      28: a8c153f3      ldp     x19, x20, [sp], #0x10
      2c: f84107f5      ldr     x21, [sp], #0x10
      30: a8c17bfd      ldp     x29, x30, [sp], #0x10
      34: d65f03c0      ret
      38: aa0203f4      mov     x20, x2
      3c: f9400280      ldr     x0, [x20]
      40: 90000001      adrp    x1, 0x0 <sum_balances>
                0000000000000040:  R_AARCH64_ADR_GOT_PAGE       balance_of
      44: f9400021      ldr     x1, [x1]
                0000000000000044:  R_AARCH64_LD64_GOT_LO12_NC   balance_of
      48: d63f0020      blr     x1
      4c: aa1503e1      mov     x1, x21
      50: ab000021      adds    x1, x1, x0
      54: 540000c2      b.hs    0x6c <sum_balances+0x6c>
      58: 91002294      add     x20, x20, #0x8
      5c: d1000673      sub     x19, x19, #0x1
      60: aa1403e2      mov     x2, x20
      64: aa0103f5      mov     x21, x1
      68: 17ffffee      b       0x20 <sum_balances+0x20>
      6c: 0000c11f      udf     #0xc11f
```

`sum_balances.relocs.json` lists exactly the two GOT relocations (offsets 64 and 68,
`Aarch64AdrGotPage21`, `Aarch64Ld64GotLo12Nc`, target `balance_of`, addend 0);
`sum_balances.traps.json` is `[{"code": "int_ovf", "offset": 108}]` (0x6c, the `udf`).
**Difference from PLAN.md's 0.130.2 observation:** at `opt_level=none` 0.136.1 lowers the
checked add + `trapnz` to `adds` / `b.hs` to an out-of-line `udf` (no `cset`/`uxtb`/`cbnz`);
the trap is still `udf #49439` (0xc11f). With `--colocated-externs` the call is
`bl` with one `R_AARCH64_CALL26` (`Arm64Call`) relocation.

## `clif-native`

```
clif-native <file.clif> [--link <obj-or-archive>]... [--keep <dir>] [--timeout <secs>]
            [--functions-obj <obj> --functions-table <json>]
```

Prints one JSON record per `; run`/`; print` comment on stdout, in exactly the clif-oracle
schema and order (`docs/contracts/clif.md`; the code is shared through `clif-runlines`):
`{"attached", "func", "args", "expected", "actual"}` with `actual` one of
`{"returned": [values]}`, `{"trapped": "<code>"}`, `{"error": "..."}`. A file the reader
rejects prints `{"file_error": "..."}` and exits 1. Exit status 0 otherwise (whatever the
outcomes); 2 for environment failures (missing tool, a `--link` file that does not exist,
a link failure not caused by undefined CLIF externs).

How it runs:

1. The file is parsed (`clif2obj::parse_file`) and each function is compiled once on its
   own; functions Cranelift rejects (verifier, unsupported lowering, panic), and functions
   calling them, are left out.
2. One object is built with `clif2obj::ObjectCompiler` (same code path and settings as
   `clif2obj`): the remaining functions plus one CLIF trampoline per invoked function,
   `__clifnative_tramp_N(i64 buf) system_v`, which loads argument `i` from `buf + 16*i`,
   calls the function with its own signature (so AAPCS64 or the function's declared
   convention is handled by Cranelift), and stores result `j` to `buf + 16*j`
   (any number of results, types up to 16 bytes).
3. A freestanding C harness (`src/harness.c`, `clang --target=aarch64-linux-gnu
   -ffreestanding -fno-builtin -nostdlib -O2`) with generated tables of the run commands
   (argument bytes, trampoline, result size) and of the compiled functions (start, size) is
   linked with the object and the `--link` files by `rust-lld -flavor gnu -static
   -e _start`, and run as `qemu-aarch64-static -s 1GiB exe START`.
4. The harness runs the commands from `START` in order and writes a binary record per
   command (results, or signal + faulting function + offset). SIGILL/SIGSEGV/SIGBUS/SIGFPE/
   SIGTRAP are caught (raw `rt_sigaction`, `sigaltstack`); the handler reports the PC, then
   rewrites the signal frame to resume at a fresh stack with the next command. `clif-native`
   maps the PC through the function's Cranelift trap table: a trap site under
   SIGILL/SIGSEGV/SIGBUS/SIGFPE gives `{"trapped": code}`; any other fault gives
   `{"error": "SIGSEGV at %f+0x0, which is not a trap site"}` (e.g. a `notrap` access to
   unmapped memory, or native stack overflow — no stack probes are enabled, so there is no
   `stk_ovf`).
5. If the process dies or produces no record for `--timeout` seconds (default 20; e.g. an
   infinite loop), the pending command gets `{"error": "the test process ..."}` and the
   process is restarted after it.

Tools: `CLIF_NATIVE_CLANG` (default `clang`), `CLIF_NATIVE_LLD` (default the active Rust
toolchain's `rust-lld`), `CLIF_NATIVE_QEMU` (default `qemu-aarch64-static`). `--keep DIR`
keeps `clif.o`, `harness.c`, `clifnative_tables.h`, `harness.o`, `test.exe`.

Linking: externs not defined in the file must come from `--link` objects or archives (the
M1 runtime is linked this way; objects must be freestanding/static aarch64 ELF — e.g.
`clang --target=aarch64-linux-gnu -ffreestanding -nostdlib -c`, or a `no_std` Rust
staticlib for `aarch64-unknown-linux-musl`). An undefined symbol is reported on stderr
(`clif-native: F.clif: unresolved external symbol `balance_of``) and every run command
reaching a function that references it (directly or through file-internal calls) gets
`{"error": "%f is not available: calls %g: unresolved external symbol `balance_of` (not
defined in F.clif and not provided by --link)"}`; the other commands still run.

Prebuilt functions (`--functions-obj OBJ --functions-table JSON`, used by the Lean backend,
`docs/contracts/backend.md`): the file's functions are **not** compiled by Cranelift (and
not checked with it); their code comes from `OBJ`, which is linked in. Cranelift still
compiles the trampolines, which call the functions through their symbols (GOT, as for any
import), so the prebuilt code must follow the functions' calling convention. `JSON` is the
object's function/trap table:

```json
{"functions": [{"name": "f", "size": 120, "traps": [{"offset": 116, "code": "int_divz"}]}],
 "unsupported": [{"name": "g", "reason": "`select.i32 v0, v1, v2` is not in E"}]}
```

`size` (bytes of the symbol `name`) and `traps` (byte offset from `name`, CLIF trap-code name)
replace Cranelift's `CompiledFunc` code length and trap table in the harness's fault mapping.
A file function missing from `functions` is excluded like a function Cranelift rejects:
`{"error": "not compiled: %g: not in the functions object: <reason>"}` (`reason` from
`unsupported` if present), and so are its callers. If the link fails on undefined symbols,
the functions calling them (by their CLIF declarations) are excluded as above and the link is
retried with `--unresolved-symbols=ignore-all` (the prebuilt object still contains those
callers, but no run reaches them). Without the two flags, behaviour is unchanged.

Error messages with a fixed prefix (counted by `clif-results`):

- `not compiled: %f: ...` — Cranelift rejects `%f` (or a function it calls) for aarch64
  with the fixed settings;
- `no function %f in the file`, `argument types ... do not match ...`,
  `%f is not available: ...` (unresolved extern, `u0:1`-style name),
  `run command does not parse: ...`.

Semantics notes:

- Commands invoke the function named in the command (as `test interpret` and
  `clif-oracle` do). Upstream `test run` instead always calls the function the comment is
  attached to; this matters only for runtests with a mismatched name (one line in
  `fcvt-sat-small.clif`).
- Run-command arguments must have the callee's parameter types (vectors: same size, as the
  reader types vector literals `i8x16`); `vmctx` parameters take the run-command argument
  as an ordinary pointer. Other special parameter purposes are rejected.
- Only the machine code is native: floats and vectors run too, but the acceptance set is
  integer-only.

## `clif-results`

- `clif-results summary [-v] FILE.json...`: per file and total `pass fail print error
  not-compiled file-error`. `pass`/`fail`: the `==`/`!=` expectation holds/does not hold
  (a trap is a fail); `not-compiled`: errors starting with `not compiled:`; `-v` lists
  every non-pass. Exit 0 iff no fail, no other error, no file error.
- `clif-results compare [-v] DIR_A DIR_B`: record-by-record comparison of same-named
  `*.json` files: `agree` (equal `actual`), `disagree` (different outcomes, neither an
  error), `error` (one side is `{"error"}`), `unmatched` (records for different commands or
  missing). Exit 0 iff no disagreement and nothing unmatched.

## Filetest results (`scripts/aarch64-native-filetests.sh`)

Default set: the 128 runtest files `clif-filetest` reports fully supported by `Clif.run`
(list in the script). Observed (`--compare`):

| | runs |
| --- | --- |
| pass | **4894** |
| fail | **0** |
| error | **0** |
| not compiled for aarch64 | 578 |
| agree with the interpreter | 4881 |
| disagree with the interpreter | 13 |
| one side error (the 578 not compiled) | 578 |

Exit status: 0 without `--compare`; 1 with `--compare` because of the 13 disagreements.

Named files: arithmetic 445, br_table 25, brif 35, call 6, div-checks 16, extend 49,
bitops 181, i128-arithmetic 51 — all pass.

Not compiled (Cranelift 0.136.1 aarch64 has no lowering, or the verifier rejects the
function for a 64-bit target; these files target other ISAs upstream): big-endian
loads/stores (alias-analysis-endianness 3, atomic-cas-subword-big 12,
atomic-rmw-subword-big 264), i128 atomics (atomic-128 93, atomic-128-cas-lse 8), i128
division/remainder (i128-srem 18, i128-urem 18, sdiv-i128 3), `*_overflow_cin` /
`*_overflow_bin` (iaddcarry 66, isubborrow 62), more return values than registers
(issue-6582 3, issue5526 1), 32-bit pointers (stack-32 18, stack-addr-32 9).

Disagreements with the interpreter (native = expectation in all 13): `div-checks.clif`
`srem MIN, -1` for i8/i16/i32 (6; interpreter traps `int_ovf`, see clif.md), and
`i128-load-store.clif` `%i128_stack_store_load_inst_offset` (7; the interpreter traps
`heap_oob` on the store 16 bytes past `ss1`, native code writes into the adjacent `ss2`
as the test expects).

`--all` (395 files, including float/vector files, for information): pass 12811, fail 20,
error 9, not compiled 893; the fails are all in float/SIMD files that target other ISAs or need ISA flags we do not set
(`has_fp16`), or with a mismatched invocation name; no integer failures.

## Limitations

- Target fixed to `aarch64-unknown-linux-gnu` in `clif-native`; ISA flags are defaults
  (file `target` flags such as `has_lse`, `has_fp16` are ignored).
- Stack overflow is not a trap (no probes/stack limit): it is reported as an error.
- One process per file; a crash or hang costs one restart (qemu start-up).
- Argument/result types wider than 16 bytes are rejected; `sret`/struct arguments too.
- Both drivers reject symbol global values and non-`%name` function names, and
  `clif-native` excludes functions whose `fnN` names a libcall (`%CeilF32`-style) or a
  `u0:1`-style name (in `--all`: 9 errors of this kind plus invocations of functions that
  do not exist or with float/vector argument mismatches in upstream files).

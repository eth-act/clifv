# Survey: the CLIF that `rustc_codegen_cranelift` produces, versus E and S

Question: if we trust Rust → CLIF via `rustc_codegen_cranelift` (cg_clif) and feed its CLIF to
our verified CLIF → AArch64 backend, how far is that CLIF from the emitter subset E and the
`Clif.run` subset S of `clif-subset-v1` (`docs/contracts/clif-subset.md`)?

Everything below was observed on 2026-09-27 unless marked **[inference]** or **[estimate]**.
Scripts are in `scripts/rust-clif/`; the full generated tables are in the appendix.

## Summary

- **cg_clif emits a small integer CLIF.** Over 933 functions (9 crates × debug / release /
  release with overflow checks, aarch64), only **48 distinct opcodes** occur: **36 in E**, **9 in
  S but not E**, **3 in neither** (`symbol_value`, `call_indirect`, `func_addr`). No floats, no
  vectors, no `*_overflow`, no `trapz`/`trapnz`, no extending loads, no `uadd_overflow_trap`.
  Overflow checks are `iadd` + `icmp`, and `umulhi`/`smulhi` for multiplication, the same
  shape E prescribes. Every trap is `trap user1`, after a call to a panic function or in a
  block that MIR marks unreachable.
- **The gap for (a)–(f)** (arithmetic, slices, enums, loops, Option/Result, crypto kernels), debug
  and release: **8 opcodes** (`nop`, `symbol_value`, `select`, `smin`, `smax`, `umin`,
  `bswap`, `bitrev`; add `umax` for symmetry). All of them except `symbol_value` are already in
  S. Beyond opcodes, cg_clif also needs `sret` parameters, calls to external panic and
  `memcpy`/`memset`/`memmove`/`memcmp` functions, **read-only data objects with relocations**
  (what `symbol_value` points at), and a few text-format fixes. With `nop`, `symbol_value`,
  `select`, min/max, `bswap` and `bitrev` added, **100 % of the (a)–(f) functions** have all
  their opcodes in the extended set (349/349 debug, 177/177 release).
- **The largest item is `symbol_value`, and its data is not in the CLIF dumps.** 152 of 454 debug
  functions use it: panic `Location`s and messages, constant tables (SHA-256 `K`), constant
  enum values such as `None`, vtables. The data objects (`allocN`) exist only inside cg_clif's
  object file, as local `.LdataN` symbols with relocations. An integration therefore needs cg_clif
  to export data descriptions, or needs our backend to run inside cg_clif; parsing its text
  dumps is not enough.
- **Version skew is a non-issue.** The nightly bundles Cranelift **0.135.0** and our pin is
  0.136.1. The opcode sets (163), `instructions.rs`, the reader and the writer are identical
  except for Rust-syntax refactors. All **1866** dumped files (unopt and opt) pass the pinned
  0.136.1 reader and verifier (`clif-oracle check`).
- **Our tools:**
  - `Clif.parseFile` rejects every raw dump, because of `u0:N` function names. After a
    semantics-preserving renaming (`normalize.py`), it accepts 60–72 %. The rejections are
    `symbol_value` and `sigN` declarations.
  - `clif2obj` compiles every function that has no data symbol: 625 of 933.
  - `lean-backend` rejects `nop` first (all functions). With `nop` dropped it compiles 368 of
    933 corpus functions and 228 of 1575 `core`/`alloc` functions.
  - End to end: 24 functions and 88 run lines, with expected values computed by rustc/LLVM.
    Lean backend on qemu: **88/88 pass**, and all 88 agree with Cranelift-native and with
    `Clif.run`.
- **Two bugs in `FV/Clif/Parse.lean`** (repro: `scripts/rust-clif/parser-repro.clif`):
  1. A value alias written after a use (`return v5` … `v5 -> v6`) stays unresolved. The parser
     accepts the function and `Clif.run` gets stuck ("use of undefined value"). This affects
     17–27 corpus functions and 185 `core`/`alloc` functions.
  2. Global values are parsed as `colocated symbol %x`, but the reader syntax is
     `symbol colocated %x`.
- **Recommendation:** feasible, and the opcode work is small. Most of the cost is in data
  objects and the ABI (`sret`), in the runtime story (core's panic machinery, `mem*`,
  allocator), and in owning a thin fork of cg_clif to get at data. **[estimate]** (a)–(f):
  about 5–8 person-weeks to a proven backend extension, on top of the current M4 plan. (g) i128
  and (h) `dyn` are 2–4 weeks each.

## 1. Setup and method

### Toolchain and versions

| Item | Value |
| --- | --- |
| Toolchain | `nightly-2026-09-26` = `rustc 1.100.0-nightly (5ceaf6608 2026-09-25)`, host x86_64-unknown-linux-gnu |
| Install | `rustup toolchain install nightly-2026-09-26 --profile minimal --component rustc-codegen-cranelift-preview,rust-src` and `rustup target add aarch64-unknown-linux-gnu --toolchain nightly-2026-09-26` (the repo's pinned `1.96.0` is untouched) |
| Backend | `lib/rustlib/x86_64-unknown-linux-gnu/codegen-backends/librustc_codegen_cranelift-1.100.0-nightly.so` |
| Bundled Cranelift | **0.135.0**: `compiler/rustc_codegen_cranelift/Cargo.toml` at `5ceaf6608` (`cranelift-codegen = "0.135.0"`, …), and `cranelift-codegen-0.135.0` strings in the `.so` |
| Our pin | Cranelift 0.136.1 (wasmtime v49.0.1, `docs/PINS.md`) |

**0.135.0 versus 0.136.1** (crates.io sources diffed against `third_party/wasmtime`):

- Same 163 opcodes.
- `meta/src/shared/instructions.rs` differs only in `operands_in(vec![…])` → `operands_in(&[…])`.
- `cranelift-reader`: only removed `use std::u16` lines.
- `codegen/src/write.rs`: identical.
- `codegen/src/ir/*`: only removed `use core::u32`-style imports.
- 50 codegen files differ. The differences include new mid-end `simplify` rules, Apple-AArch64
  stack-argument extension, and an aarch64 `AtomicCAS128` refactor.
- `stack_load`/`stack_store` are not opcodes in 0.135.0 either (only builder conveniences that
  expand to `stack_addr` + `load`/`store`). The `stack_store` in the doc comment of cg_clif's
  `pretty_clif.rs` is stale.

### How to dump CLIF from cg_clif

cg_clif writes CLIF whenever `llvm-ir` is among the requested outputs (`pretty_clif.rs`:
`should_write_ir` = `output_types.contains_key(&OutputType::LlvmAssembly)`). For each function
it writes into `<output>.clif/`:

- `<symbol>.unopt.clif`: the frontend's output, after `FunctionBuilder::finalize` and before
  Cranelift's `Context::compile`;
- `<symbol>.opt.clif`: `context.func` after compilation (egraph mid-end if enabled,
  legalisation);
- `<symbol>.vcode`: the lowered machine code.

Files carry `set …`/`target …` headers and long `; abi`/`; instance` comments. Exact command:

```sh
rustc +nightly-2026-09-26 -Zcodegen-backend=cranelift --target aarch64-unknown-linux-gnu \
  --edition 2021 --crate-type lib --crate-name a_arith -Cpanic=abort \
  -Zunstable-options -Csymbol-mangling-version=hashed -Ccodegen-units=1 \
  -Copt-level=0 -Cdebug-assertions=on -Coverflow-checks=on \
  --emit=llvm-ir,obj --out-dir OUT a_arith.rs
# -> OUT/a_arith.clif/<symbol>.{unopt,opt}.clif, OUT/a_arith.o
```

- rustc then fails with `could not copy "….rcgu.ll"` (exit 1), because cg_clif never writes the
  `.ll` file. The CLIF files and the object are complete by then; `dump.sh` ignores exactly that
  error. With several CGUs (e.g. under cargo) rustc does not try the copy.
- `-Csymbol-mangling-version=hashed` is needed because file names are symbol names, and v0 names
  of monomorphised iterator adapters exceed the 255-byte limit (`error writing ir file: File
  name too long`). `#[no_mangle]` functions keep their names.
- **Cross-dumping works.** An x86_64-hosted cg_clif targets `aarch64-unknown-linux-gnu`
  directly (the backend is built with `all-native-arch`), so all corpus CLIF is aarch64 CLIF:
  `target aarch64`, `system_v` call conv, `i64` pointers.
- Other knobs:
  - `CG_CLIF_ENABLE_VERIFIER=1` (or `-Zverify-llvm-ir`) runs the Cranelift verifier.
  - `-Cllvm-args=jit-mode` selects JIT mode.
  - `CG_CLIF_JIT_ARGS` passes arguments in JIT mode.

  There is no other dump switch (`config.rs`).
- Under cargo: `CARGO_PROFILE_DEV_CODEGEN_BACKEND=cranelift cargo +nightly build
  -Zcodegen-backend` plus `RUSTFLAGS=--emit=llvm-ir` (`scripts/rust-clif/core.sh` uses a
  `RUSTC_WRAPPER` instead, to exempt `compiler_builtins`).

### What cg_clif sets and optimises (`src/lib.rs` `build_isa`, `src/optimize/`)

- **Cranelift flags:**
  - `opt_level=none` for `-Copt-level=0` and **`speed_and_size` for every other level**;
  - `is_pic=true`, `preserve_frame_pointers=true`;
  - `enable_probestack=true` with `probestack_strategy=inline` on aarch64 and x86_64;
  - `tls_model=elf_gd`, `enable_llvm_abi_extensions=true`, `unwind_info=true`;
  - the verifier is off unless requested.
- **cg_clif's own optimisations** are minimal: `optimize/peephole.rs` folds `bool` negation
  into branches and statically known branches while building CLIF.
- **At `-O`, the rest is rustc's MIR pipeline** (MIR inliner, GVN, simplify-cfg). Release has
  fewer functions: 239 versus 454, because MIR inlining folds small core helpers.
- **Unwinding** is compiled out of the distributed backend. `codegen_call_with_unwind_action`
  forces `UnwindAction::Unreachable` unless cg_clif's `unwinding` Cargo feature is on, which it
  is not by default. A `-Cpanic=unwind` build with `Drop` types emitted plain `call`s, no
  `try_call`.

### Corpus (`scripts/rust-clif/corpus/*.rs`, `#![no_std]` except `i_alloc`, which uses `alloc`)

| Crate | Content |
| --- | --- |
| `a_arith` | `+ - * neg` (overflow-checked in debug), wrapping/checked/overflowing/saturating, `/ %` (incl. const divisor, `checked_div`), shifts, rotate, clz/ctz/popcnt, `swap_bytes`/`reverse_bits`, `abs`, casts, min/max, `pow` |
| `b_slices` | indexing with bounds checks, `get`, arrays by value and returned (`[u8; 64]`), `copy_from_slice`, `fill`, `split_at`, `swap`, insertion sort, `from_le/be_bytes`, `try_from`, slice `==`, a bounded buffer |
| `c_structs_enums` | small/large structs by value (sret), data-carrying enums, `repr(u8)` enum, sparse and dense `match`, niche `Option<&T>`, nested options, `char` classes |
| `d_loops_iters` | ranges, `while`, `fold`/`map`/`filter`/`zip`/`enumerate`/`rev`/`step_by`/`position`/`any`/`chunks_exact`/`count`, labelled break |
| `e_option_result` | `?` on Option and Result, a digit parser with checked arithmetic, combinators, `unwrap`, `expect` (with `#[derive(Debug)]`) |
| `f_crypto` | ChaCha20 quarter round and block (10 double rounds), SHA-256 compression, constant-time compare |
| `g_u128` | u128/i128 add, mul, shifts, compare, `/ %`, `checked_mul`, widening `u64×u64`, `from_le_bytes`, clz/popcnt, Poly1305-style limb MAC |
| `h_dyn_generic` | generic `H: Hasher` (two instances), `&mut dyn Hasher`, `fn` pointers, a table of `fn` pointers, `&dyn Fn`, generic closures, `&[&dyn Area]` |
| `i_alloc` | `Vec` push/iter, `Box<[u64; 4]>` |

Profiles:

- **debug:** `-Copt-level=0 -Cdebug-assertions=on -Coverflow-checks=on`
- **release:** `-Copt-level=3 -Cdebug-assertions=off -Coverflow-checks=off`
- **release-oc:** release plus `-Coverflow-checks=on`

All profiles use `-Cpanic=abort`, `-Ccodegen-units=1` and target aarch64. Functions include core
generics instantiated in the crate. Of 454 debug functions, 169 are the crate's own items and
285 are core/alloc instantiations such as `Iterator::next`, `checked_add` or intrinsic fallback
bodies. In release the split is 147 / 92.

In addition, `scripts/rust-clif/core.sh` compiles **`core` and `alloc` themselves** with cg_clif
(`-Zbuild-std`, release): 1237 + 338 non-generic functions, the library code every Rust binary
links. That dump targets x86_64, because on aarch64 cg_clif stops with `128bit atomics not yet
supported` in `core::sync::atomic`, and `compiler_builtins` must stay on LLVM (cg_clif fails on
its `f128` code). CLIF is target-independent apart from the pointer type, the call conv and ISA
flags **[inference]**; the corpus confirms `i64` pointers and `system_v` on both targets.

### Analysis

- `analyze.py` parses every `.clif`. It collects opcode histograms, types, memory flags, trap
  codes and their predecessors, `icmp` codes, callees classified by the symbol cg_clif records
  in each `fnN` comment, call conventions, ABI attributes, stack slots, global values and
  per-function features.
- `tools.sh` runs `clif-oracle check`, `Clif.parseFile` (via `ParseCheck.lean`), `clif2obj` and
  `lean-backend`.
- `smoke.sh` runs a differential end-to-end test.

## 2. What cg_clif emits (corpus)

### Size

| profile | functions | crate's own items | instructions (unopt) | blocks | cold blocks |
| --- | --- | --- | --- | --- | --- |
| debug | 454 | 169 | 17701 | 2873 | 324 |
| release | 239 | 147 | 10687 | 1609 | 142 |
| release-oc | 240 | 148 | 11486 | 1768 | 219 |

### Opcodes, classified against E and S (unopt, instruction counts)

**(i) In E: 36 opcodes.**

| opcode | debug | release | opcode | debug | release |
| --- | --- | --- | --- | --- | --- |
| `stack_addr` | 3269 | 2101 | `br_table` | 66 | 36 |
| `load` | 1991 | 1336 | `isub` | 61 | 45 |
| `iconst` | 1706 | 1197 | `ishl` | 43 | 10 |
| `store` | 1635 | 1086 | `bor` / `bxor` / `band` | 41 / 39 / 23 | 12 / 34 / 18 |
| `jump` | 1335 | 698 | `umulhi` / `smulhi` | 16 / 1 | 1 / 1 |
| `call` | 750 | 273 | `udiv` / `urem` / `sdiv` / `srem` | 14 / 7 / 2 / 1 | 12 / 7 / 2 / 1 |
| `return` | 620 | 373 | `ushr` / `sshr` | 12 / 3 | 12 / 3 |
| `icmp` | 524 | 278 | `popcnt` / `clz` / `ctz` | 9 / 3 / 1 | 3 / 3 / 1 |
| `brif` | 497 | 280 | `sextend` | 5 | 3 |
| `trap` | 355 | 222 | `rotl` / `rotr` | 4 / 1 | 7 / 10 |
| `iadd` | 294 | 303 | `ineg` / `bnot` | 2 / 1 | 2 / 1 |
| `imul` | 249 | 251 | | | |
| `ireduce` / `uextend` | 110 / 79 | 63 / 59 | | | |

Never used: `uload*`, `sload*`, `istore*`. cg_clif loads and stores at the value's own type and
widens with `uextend`/`sextend`.

**(ii) In S but not E: 9 opcodes.**

| opcode | debug | release | where it comes from |
| --- | --- | --- | --- |
| `nop` | 3480 | 1738 | cg_clif's anchor for its comments; no semantics |
| `select` | 23 | 13 | saturating ops, niche-encoded enum discriminants (`Option<&T>`, nested `Option`), `enumerate`, `overflowing_pow` |
| `iconcat` | 5 | 5 | building `u128` from two `u64` halves (g only) |
| `bswap` | 3 | 3 | `from_be_bytes`, `swap_bytes` (b, f, a) |
| `umin` / `umax` / `smin` / `smax` | 2 / 2 / 1 / 1 | same | `Ord::min`/`max` intrinsics, `zip` length |
| `bitrev` | 1 | 1 | `reverse_bits` |

**(iii) In neither: 3 opcodes.**

| opcode | debug | release | uses | `Clif.parse` |
| --- | --- | --- | --- | --- |
| `symbol_value` | 405 | 168 | panic `Location`/message data, constant tables, constant aggregates (`None`), vtables | rejected: `unsupported: opcode symbol_value` |
| `call_indirect` | 7 | 7 | `dyn` method calls (vtable load `notrap aligned readonly`), `fn` pointers, `&dyn Fn` | rejected (`sigN` declaration first, then `opcode call_indirect`) |
| `func_addr` | 2 | 2 | a table of `fn` pointers | rejected: `opcode func_addr` |

**Class shares** (distinct opcodes / instruction share):

| profile | stage | E | S\E | neither |
| --- | --- | --- | --- | --- |
| debug | unopt | 36 / 77.8 % | 9 / 19.9 % | 3 / 2.3 % |
| release | unopt | 36 / 81.8 % | 9 / 16.5 % | 3 / 1.7 % |
| release | opt | 35 / 93.7 % | 9 / 4.0 % | 3 / 2.4 % |

**Non-E opcodes per category**, debug / release (unopt):

| category | debug | release |
| --- | --- | --- |
| (a) arith | nop, symbol_value×40, select×4, bswap, bitrev, smin, smax, umin | nop, symbol_value×12, select×4, smin, smax, umin, bswap, bitrev |
| (b) slices | nop, symbol_value×55, bswap, select | nop, symbol_value×23, bswap |
| (c) structs/enums | nop, symbol_value×8, select×2 | nop, symbol_value×3, select×2 |
| (d) loops/iters | nop, symbol_value×67, select×3, umin | nop, symbol_value×26, select×2, umin |
| (e) Option/Result | nop, symbol_value×19, select×5 | nop, symbol_value×17 |
| (f) crypto | nop, symbol_value×114, bswap | nop, symbol_value×60, bswap |
| (g) u128 | nop, symbol_value×30, iconcat×5 | nop, iconcat×5, symbol_value×4 |
| (h) generic/dyn | nop, symbol_value×16, call_indirect×7, select×3, func_addr×2 | nop, symbol_value×8, call_indirect×7, func_addr×2 |
| (i) alloc | nop, symbol_value×56, select×5, umax×2 | nop, symbol_value×15, select×5, umax×2 |

**Opcode coverage per function (unopt):**

| profile | functions | only E | only E + `nop` | only S |
| --- | --- | --- | --- | --- |
| debug | 454 | 0 | 279 | 298 |
| release | 239 | 0 | 163 | 172 |
| release-oc | 240 | 0 | 136 | 143 |

### Non-opcode features

- **Types:** `i8 i16 i32 i64` everywhere and `i128` only in (g). i128 appears in 13 debug
  functions, as params and returns, `load`/`store`, `iadd`, `imul`, shifts, `icmp`, `clz`,
  `popcnt` and `uextend.i128`. Division, remainder and `checked_mul` go through the libcalls
  `__udivti3`, `__modti3` and `__rust_u128_mulo`. No floats or vectors in the corpus.
- **Memory flags:**
  - every `load`/`store` is `notrap` (debug 3626 of 3626);
  - 64 (1.8 %) are also `aligned`;
  - vtable loads are `notrap aligned readonly`.

  No `heap_oob` accesses. Safety of every access is Rust's guarantee, not a local fact.
- **Traps:** only `trap user1` (debug 355, release 222). Debug: 256 follow a call to a panic
  function, which never returns, and 99 are MIR-unreachable blocks. No `trapz`/`trapnz`, no trap
  codes other than `user1`.
- **Checked arithmetic:**
  - debug `a + b` on `u32` is `iadd` + `icmp ult` + `brif` to a cold block that calls
    `panic_const_add_overflow(&Location)`;
  - signed `checked_mul` is `imul` + `smulhi` + `sshr 63` + `bxor` + `icmp ne`;
  - `/` and `%` are guarded by an explicit zero test (and a `MIN / -1` test for signed) in
    **both** debug and release, so the `udiv`/`sdiv` trap is unreachable;
  - shifts are range-checked in debug; in release they rely on CLIF's modulo masking.
- **Calls:** debug 750 `call`s by callee kind:
  - Rust functions of the same crate (colocated): 451;
  - panic paths: 255 (`panic_bounds_check`, `panic_const_*`, `panic_fmt`, `panic_nounwind_fmt`
    from debug UB checks, `unwrap_failed`, `slice_index_fail`, `len_mismatch_fail`);
  - Cranelift libcalls: `Memcpy` 14, `Memset` 4, `Memmove` 2;
  - `memcmp` by name: 1;
  - compiler-builtins helpers: 9;
  - upstream Rust functions: 8;
  - allocator shims (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`,
    `__rust_no_alloc_shim_is_unstable_v2`).
- **Calling convention:** only `system_v` (AAPCS64 on aarch64), explicit on every signature.
- **ABI attributes:** `uext` on `bool`/`u8` params and returns (56 functions) and **`sret`**
  (29 debug functions). Up to 7 params and 2 returns in the corpus; `core` has up to 23 params,
  so some arguments go on the stack.
- **Stack slots:** only `explicit_slot`: 873 slots in 267 of 454 debug functions, sizes 1–256
  bytes, `align` ≤ 8. In `core` they go up to 1024 bytes with `align = 16`. Unopt CLIF is
  stack-heavy: `stack_addr` + `load` + `store` are 39 % of debug instructions, because every
  non-SSA MIR local lives in a slot.
- **Global values:** only `symbol colocated userextnameN` (401 `allocN`, 4 vtables in debug).
  `core` adds non-colocated `symbol` for statics and tables. A TLS probe gives
  `symbol tls userextnameN` + `tls_value`; atomics give `atomic_rmw`.
- **Text-level quirks:**
  - functions are named `u0:N` (FuncIds numbered across the module);
  - callees are declared as `fnK = [colocated] u0:N sigM`, with a separate `sigM`;
  - Cranelift libcalls appear as `%Memcpy`;
  - `cold` blocks;
  - value aliases `vA -> vB`, in 398 of 454 debug functions. 17 debug, 21 release and 27
    release-oc functions place an alias **after** a use in layout order. This is legal CLIF and
    the reader accepts it.

### unopt versus opt

At `opt_level=speed_and_size` (release) the egraph mid-end removes about 40 % of the
instructions: 10687 → 6533, of which `nop` 1738 → 239, `stack_addr` 2101 → 979, `imul` 251 → 42
and `load` 1336 → 801. It introduces **no opcode that unopt lacks**. At `opt_level=none`
(debug), opt differs from unopt only by alias resolution and some `nop`s. **[inference]** The
interface to trust is `unopt`, i.e. cg_clif's output; `opt` would also trust Cranelift's
mid-end.

## 3. Library code: `core` and `alloc` compiled by cg_clif

| | functions | instructions (unopt) | E ops / share | S\E ops / share | neither ops / share |
| --- | --- | --- | --- | --- | --- |
| core | 1237 | 100471 | 33 / 82.7 % | 10 / 15.1 % | 12 / 2.3 % |
| alloc | 338 | 25187 | 27 / 85.8 % | 4 / 13.1 % | 3 / 1.0 % |

- **Additions over the corpus:**
  - `atomic_load` (33) and `atomic_store` (3), both `notrap aligned`;
  - `bitcast` (19) and `isplit` (3);
  - floats: `fcmp`, `f16const`/`f32const`/`f64const`, `fcvt_from_uint`, `fdiv`, `fmul`,
    `fabs`, `fneg`, and the libcalls `__extendhfsf2`/`__truncsfhf2`. Floats occur in 78 of
    1237 functions (`f16`/`f32`/`f64` types);
  - `func_addr` in 38 functions and `call_indirect` in 34.
- **`symbol_value`** appears in 500 of 1237 functions. Besides `allocN`, it points at static
  tables (`DECIMAL_PAIRS`, Grisu/Dragon powers, Unicode tables).
- **`sret`** appears in 147 functions.
- **Forward aliases** occur in 152 functions.

**[inference]** Float formatting and parsing in core are integer algorithms. The float surface is
small: `f32`/`f64` methods, and `f16` conversions via libcalls.

## 4. Comparison with E and S, and our parser

- **(i)/(ii)/(iii)** are listed with counts in §2. Union over all profiles of the corpus: 36 E,
  9 S\E, 3 neither. `core`/`alloc` add 4 S\E opcodes (`atomic_load`, `atomic_store`, `bitcast`,
  `isplit`) and 9 more in neither (floats).
- **Text differences from the Cranelift version: none.** 1866 of 1866 raw files (unopt and opt,
  including the `set`/`target` headers cg_clif writes, `userextnameN`, `u0:N`) pass the pinned
  reader and verifier.
- **`Clif.parseFile` on the raw dumps:** 933 of 933 functions rejected with
  `unsupported: function name 'u0' (only %names)`.
- **`normalize.py`**: purely textual; the output is re-checked by `clif-oracle check` and 0
  files are rejected. It:
  - renames functions to their symbols;
  - inlines `sigN` into `fnN = %sym(sig)` and drops `sigN` unless a `call_indirect` uses it;
  - maps `%Memcpy` → `%memcpy`;
  - names data `%allocN`;
  - drops comments.

  Lean parse after normalising:

| profile (unopt) | accepted | unsupported |
| --- | --- | --- |
| debug | 298 / 454 | 156 |
| release | 172 / 239 | 67 |
| release-oc | 143 / 240 | 97 |

  Rejection reasons, all profiles: `opcode symbol_value` 305, `declaration 'sigN'` 15
  (`call_indirect`). `core`/`alloc`: 898 of 1575 accepted; rejections are `symbol_value` 523,
  `func_addr` 38, `sigN` 38, float types 78.
- **Parser bugs found** (both reproduced in `scripts/rust-clif/parser-repro.clif` with
  `clif-filetest`; the Cranelift interpreter passes both functions):
  1. **Forward value aliases are not resolved.** `resolveAlias` in `FV/Clif/Parse.lean` only
     sees aliases parsed so far. A use before `vA -> vB` keeps `vA`, the function is accepted,
     and `Clif.run` gets stuck: `FAIL %f(2) == 4: stuck (use of undefined value v5)`. Lean
     backend symptoms are `value_type of unknown vN`, `put_in_reg(s_vec)` and `unknown value
     vN`. Affected: 17 / 21 / 27 corpus functions and 185 core/alloc functions. Fix: resolve
     aliases after the whole function is read.
  2. **Global value syntax.** The parser accepts `gvN = colocated symbol %x`, but the reader and
     writer syntax is `gvN = symbol [colocated] [tls] %x[+off]`
     (`cranelift/reader/src/parser.rs`, `parse_global_value_decl`). Every cg_clif global is
     therefore rejected as `function name 'colocated'`. `normalize.py --lean-gv-order` works
     around it for the Lean tools.

## 5. Through our tools (`scripts/rust-clif/tools.sh`)

- **`clif2obj`** (pinned Cranelift, aarch64), one normalised function per file:
  - debug 302 / 454, release 176 / 239, release-oc 147 / 240 compiled;
  - **every** failure is `symbol global value %allocN is not supported (only fnN function
    references are)` (308);
  - whole-crate files also hit `expected a %name callee, got LibCall(Memset)` before
    `normalize.py` maps libcalls to symbols;
  - `call_indirect`, `func_addr`, `sret`, i128 and `uext` all go through.
- **`lean-backend`**, as dumped: 0 of 933. Every function contains `nop` (`` `nop` is not in
  E ``).
- **`lean-backend` with `nop` dropped** (`normalize.py --drop-nop`): debug 171 / 454,
  release 108 / 239, release-oc 89 / 240 compiled. Remaining reasons, all profiles:

| reason | functions |
| --- | --- |
| `opcode symbol_value` | 305 |
| calls a function of the file that is not compiled | 127 |
| special-purpose parameter (`sret`), including 15 `gen_call_args` | 54 |
| `select` not in E | 22 |
| `declaration 'sigN'` (`call_indirect`) | 15 |
| i128 parameter / return / `extend to i128` | 18 |
| forward-alias parser bug (`value_type of unknown`, `put_in_reg`, `put_in_regs_vec`) | 14 |
| `bswap`, `smin`/`smax`/`umin`, `bitrev` not in E | 10 |

  No fired ISLE rule is outside the emitter-subset closure. `core`: 176 / 1237 compiled,
  `alloc`: 52 / 338.
- **End-to-end smoke** (`scripts/rust-clif/smoke.sh`):
  - input: the release functions the Lean backend compiles that have scalar signatures, plus
    their callees. That is 24 functions from (a), (c), (d) and (h): arithmetic incl. `MIN`
    edge cases, masking shifts, `rotate_left`, bit counts, casts, a `repr(u8)` enum `match`,
    sparse and dense `match` (`br_table`), `char` classes, loops, a generic closure, and a
    2-value return;
  - expected values: 88 `; run:` lines computed by **the same Rust source compiled by rustc's
    LLVM backend**;
  - `clif-filetest` (`Clif.run`): **88 pass**, 88 agree with Cranelift's interpreter;
  - `lean-backend-filetests.sh` (Lean backend → `llvm-mc` → qemu): **88 pass**, 88 agree with
    Cranelift-native.

  So, for this slice, Rust source → cg_clif → our backend already agrees with rustc/LLVM.

### Post-v2 (2026-09-27, `clif-subset-v2` in the Lean backend, `docs/contracts/e-ext-v2.md`)

Re-run of `dump.sh` + `tools.sh` + `smoke.sh` (same nightly/cg_clif, corpus unchanged) with
`nop` **kept** (`*.unopt.reader.clif`, the normalised files as dumped); the `--drop-nop`
variant (`*.unopt.nonop.clif`) gives identical counts, so `nop` no longer costs anything.

- Lean parse: 918 / 933 unopt functions (15 `call_indirect` `declaration 'sigN'`).
- `clif2obj`: 933 / 933 (phase 1 added data symbols; was 625 / 933).
- **`lean-backend`: 760 / 933** (debug 383 / 454, release 188 / 239, release-oc 189 / 240);
  before v2: 0 / 933 as dumped, 368 / 933 with `nop` dropped. Remaining reasons (all
  profiles; first reason per function):

| reason | functions |
| --- | --- |
| special-purpose parameter (`sret`), incl. 30 `gen_call_args` | 99 |
| i128 parameter / return / `extend to i128` | 34 |
| calls a function of the file that is not compiled | 25 |
| `declaration 'sigN'` (`call_indirect`) | 15 |

- **core / alloc: 267 / 1575** (core 199 / 1237, alloc 68 / 338; before: 228 / 1575 with
  `nop` dropped). Lean parse 1408 / 1575. Unsupported reasons: calls a function that is not
  compiled 801, `sret` 201 (+98 `gen_call_args`), `func_addr` 51, `declaration 'sigN'` 38,
  `f16/f32/f64` 26 each, `load.i128` 16, i128 parameter/return/extend 13, atomics 13.
- Smoke (`smoke.sh`, now without `--drop-nop`): 24 functions, 88 run lines: `Clif.run` 88
  pass / 88 agree with the interpreter; Lean backend (regalloc2, Lean-written objects) 88
  pass / 88 agree with Cranelift-native. The smoke's selection (scalar signatures, no data
  objects) is unchanged, so the same 24 functions are picked.

Next blockers in order: `sret`/special-purpose parameters, callee closure (follows), i128,
`call_indirect`, then `func_addr` and floats for core.

## 6. Runtime and ABI pieces Rust code needs beyond CLIF

Undefined symbols of the corpus objects (`nm -u`, union over the crates):

- **Panic entry points in `core`** (about 25, all diverging):
  - `panic_bounds_check`, `panic_const_{add,sub,mul,neg,div,rem,shl,shr}_overflow`,
    `panic_const_{div,rem}_by_zero`, `panic_fmt`, `panic`, `panic_nounwind(_fmt)`;
  - `option::unwrap_failed`, `result::unwrap_failed`, `slice_index_fail`,
    `copy_from_slice_impl::len_mismatch_fail`, `overflow_panic::pow`;
  - through `#[derive(Debug)]` + `expect`: `core::fmt::Formatter::{write_str,
    debug_tuple_field1_finish}` and integer `Display`/`LowerHex`/`UpperHex`.

  With `panic=abort`, these end in the `#[panic_handler]`, which for `no_std` must be provided.
  **[inference]** Either (1) trust an LLVM-compiled `core` for these (they never return, so a
  contract "does not return" is all the caller proof needs), or (2) compile `core` through
  cg_clif + our backend, which is §3's opcode surface including floats, `func_addr` and
  `call_indirect` for `fmt`.
- **`memcpy`, `memset`, `memmove`, `memcmp`:** Cranelift libcalls for aggregate copies and
  fills, and `memcmp` for slice `==`. They need a (verified or trusted) runtime implementation
  and a contract in `Clif.run`'s `Env.extern`.
- **`compiler_builtins`:** `__udivti3`, `__modti3`, `__umodti3`, `__rust_u128_mulo` (i128);
  `__extendhfsf2`, `__truncsfhf2` (f16, core only). cg_clif cannot compile compiler_builtins
  itself, so it stays LLVM-compiled.
- **Allocator:** `__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`,
  `__rust_no_alloc_shim_is_unstable_v2`, plus `alloc::alloc::handle_alloc_error` and
  `alloc::raw_vec::handle_error`. The shim is generated at link time by rustc for the final
  binary. The repo's `flat-runtime`/`extrt` path already links a Rust runtime.
- **Data objects:** every `symbol_value` target: panic `Location { file: &str, line, col }`
  with relocations to string data, messages, constant tables, vtables (function pointers plus
  size and align). In the object they are local `.LdataN` symbols in `.rodata` or
  `.data.rel.ro`; the debug `a_arith.o` has 27 `r` + 27 `d` symbols. **They are not in the
  `.clif` dumps.**
- **TLS:** `thread_local!` gives `gv = symbol tls` + `tls_value` (general-dynamic ELF TLS,
  `tls_model=elf_gd`); needed only for `std`.
- **Unwinding:** none. The distributed cg_clif has no `try_call` (the `unwinding` feature is
  off), so treat Rust as `panic=abort`. Compile with `-Cpanic=abort`.
- **Stack probes:** cg_clif enables inline probestack (4 KiB pages). The corpus maximum frame is
  well below (slots ≤ 256 B; core ≤ 1 KiB), but a backend must probe or reject frames ≥ 4 KiB.
- **ABI:**
  - AAPCS64 `system_v`;
  - `sret` in `x8`;
  - `uext` for `bool`/`u8` returns;
  - two-register returns (`ScalarPair`);
  - more than 8 integer args go on the stack (core);
  - i128 in register pairs.

## 7. Minimal E extension covering (a)–(f), debug and release

Opcodes (all but `symbol_value` already in S):

| Add to E | Why (functions of (a)–(f), summed over the three profiles) | In S | VeriISLE CLIF spec at pin | aarch64 lowering (ISLE) |
| --- | --- | --- | --- | --- |
| `nop` | every function | yes | no | `(lower (nop))` → nothing |
| `symbol_value` | 229 functions of (a)–(f) (panic data, tables, constants) | **no** | no | `load_ext_name` → `LoadExtNameGot`/`Near` (already MInsts) |
| `select` | 25 functions (saturation, niches) | yes | **no spec** (tag only) | `lower_select` → `cmp` + **`csel`** (no `CSel` MInst yet) |
| `smin` `smax` `umin` (`umax`) | 6 functions | yes | yes | `lower_select` after `emit_icmp` (scalar rules `umin 2` …) |
| `bswap` | 9 functions | yes | yes | `rev16`/`rev32`/`rev64` (`BitRR`, exists) |
| `bitrev` | 3 functions | yes | no | `rbit` (+ `lsr` for i8/i16) |

With these, every (a)–(f) function's opcodes are covered: 349 of 349 debug, 177 of 177 release,
178 of 178 release-oc.

Non-opcode additions:

1. `sret` special-purpose parameter: callee and call sites, `x8`.
2. Global-value declarations `gvN = symbol [colocated] %name[+off]`, and a **data model** in
   `Clif.run`: an initial memory image of read-only and relocated objects at symbol addresses.
3. Calls to external symbols with contracts:
   - panics: diverging;
   - `mem*`: the obvious memory effect.
4. `trap` after a diverging call and in MIR-unreachable blocks.
5. `notrap` on all accesses, justified by the trusted frontend rather than locally (E's "only
   when justified" rule cannot be met locally for Rust).

Text-level fixes, no semantics:

- the two parser bugs;
- accept `u0:N` names and `sigN` declarations (or keep `normalize.py` in the trusted base);
- drop comments.

Nothing else is needed for (a)–(f): no i128, no floats, no `call_indirect`.

- For **(g)**, add i128 on the integer ops, `iconcat`, and the libcalls `__udivti3`/`__modti3`/
  `__rust_u128_mulo`.
- For **(h)**, add `call_indirect`, `func_addr`, `sigN`, and vtables (data with function
  relocations).
- For **(i)**, add `umax` and the allocator externs.

## 8. Recommendation and effort

**Recommendation.** Using cg_clif as the trusted Rust frontend is technically a good fit:

- its unopt CLIF is almost entirely E already;
- it checks overflow the way E does;
- it never relies on CLIF traps for Rust semantics: every trap is `trap user1`, which Rust
  guarantees unreachable.

The work is not in isel. It is in the interface:

1. **Take cg_clif's `unopt` CLIF, not `opt`**, so Cranelift's mid-end stays out of the trusted
   base; `opt` adds no opcodes.
2. **Integrate at the `cranelift-module` level, not at the text dump.** Data objects and their
   relocations exist only in cg_clif's module. Carry a thin cg_clif fork (in-tree at
   `compiler/rustc_codegen_cranelift`; small relative to rustc) that writes each function's unopt CLIF and a
   data manifest (bytes, relocations, alignment, read-only flag) and links our backend's
   objects. Another option is to call the Lean backend from inside `define_function`.
   **[inference]**
3. **Pin the frontend:** nightly date plus cg_clif commit. cg_clif follows Cranelift releases
   one step behind our pin, and the text format was identical this time; re-run
   `scripts/rust-clif/` on each bump.
4. **Keep Rust `panic=abort`, and treat `core`'s panic paths as trusted diverging externs at
   first.** Compiling `core` itself through our backend adds floats and indirect calls: 12
   opcodes outside S.

**Effort [estimate]**, relative to the current M4 state (unproven backend, ISLE-interpreting
isel, stack-slot allocation). "Proof" means M4-style per-rule lemmas plus changes to `Clif.run`
and the state relation.

| Package | Opcodes to add to E | Lean backend isel | Proof obligations | Size |
| --- | --- | --- | --- | --- |
| P0 text/interface | — | — | none (fix the two parser bugs; `u0:N`, `sigN`, libcall names in `Parse.lean` or keep `normalize.py` trusted) | 2–4 days |
| P1 `nop` | 1 | trivial rule | trivial | < 1 day |
| P2 pure ops | `select`, `smin`, `smax`, `umin`, `umax`, `bswap`, `bitrev` (7) | add `CSel` MInst + asm; about 12 scalar rules (`select` 1, min/max 4, `bswap` 3, `bitrev` 4) and `lower_select` helpers into the closure | per-width `bv_decide` lemmas; write CLIF specs for `select` and `bitrev` (none at pin) and cross-read | 1–2 weeks |
| P3 `sret` and ABI | — | special-purpose param in `Args`/`Rets`/`gen_call_args` (`x8`); stack-passed args if core is in scope | state relation for `x8` and the out-pointer | 1 week |
| P4 data and `symbol_value` | 1 (+ `gv symbol` decls) | `symbol_value` → `LoadExtNameGot`/`Near` (exist); asm/relocs for data refs | `Clif.run` memory gets a link-time image (objects, contents, relocations; read-only); lemma that the materialised address equals the symbol's address (linker trusted as in M7); frontend fork to export data | 2–4 weeks |
| P5 externs and traps | — | calls to panics/`mem*` already lower | extern contracts (diverges; `memcpy`/`memset`/`memmove`/`memcmp` effects) in `Env.extern`; `trap user1` unreachable after divergence; theorem conditional on no stuck state (`notrap`) | 1 week |
| **(a)–(f) total** | **9 opcodes** (8 + `umax`) | | | **about 5–8 weeks** |
| (g) i128 | `iconcat`, i128 variants of 11 ops | multi-register `ValueRegs` paths, i128 ABI pairs, i128 rules outside the default VeriISLE run | 128-bit lemmas (larger `bv_decide`) | 2–4 weeks |
| (h) `dyn`, `fn` pointers | `call_indirect`, `func_addr` | `CallInd` exists; `sigN` | `Clif.run` function-address map; vtable data (P4) | 1–2 weeks |
| `core` through our backend | + floats (9 opcodes), atomics, `bitcast`, `isplit` | float MInsts, FP regs in the allocator | float semantics (IEEE) in `Clif.run` and the Arm model | months; defer (trust LLVM-compiled `core`) |

## 9. Reproduction

```sh
scripts/rust-clif/dump.sh                 # corpus -> /tmp/rust-clif-survey/out (3 profiles × 9 crates)
scripts/rust-clif/core.sh                 # core + alloc -> /tmp/rust-clif-survey/core/clif
python3 scripts/rust-clif/analyze.py /tmp/rust-clif-survey/out \
  --extra core=/tmp/rust-clif-survey/core/clif/core --extra alloc=/tmp/rust-clif-survey/core/clif/alloc
scripts/rust-clif/tools.sh                # reader check, Lean parse, clif2obj, lean-backend (needs built tools)
scripts/rust-clif/smoke.sh                # Rust/LLVM-derived run lines: Clif.run + Lean backend on qemu
.lake/build/bin/clif-filetest -v scripts/rust-clif/parser-repro.clif   # the two parser bugs
```

Files:

- `corpus/*.rs`: the nine crates;
- `dump.sh`: runs cg_clif;
- `normalize.py`: text normalisation (`--lean-gv-order`, `--drop-nop`, `--split`);
- `analyze.py`: the tables;
- `ParseCheck.lean`: `Clif.parseFile` per function;
- `tools.sh`, `smoke.sh` and `smoke/gen_runs.rs`: expected values from rustc/LLVM;
- `core.sh`;
- `parser-repro.clif`.

Wall-clock times: the full corpus dumps in about 2 s, core + alloc in about 9 s, and `tools.sh`
takes about 20 s.

## Appendix: generated tables (`analyze.py` output)

<!-- generated: python3 scripts/rust-clif/analyze.py /tmp/rust-clif-survey/out --extra core=… --extra alloc=… -->

### Corpus

#### Size (unopt CLIF)

| profile | functions | of which the crate's own items | instructions | blocks | cold blocks |
| --- | --- | --- | --- | --- | --- |
| debug | 454 | 169 | 17701 | 2873 | 324 |
| release | 239 | 147 | 10687 | 1609 | 142 |
| release-oc | 240 | 148 | 11486 | 1768 | 219 |

#### Opcode histogram (all functions)

| opcode | class | debug unopt | release unopt | release-oc unopt | debug opt | release opt | release-oc opt |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `nop` | S\E | 3480 | 1738 | 1970 | 3416 | 239 | 240 |
| `stack_addr` | E | 3269 | 2101 | 2180 | 3217 | 979 | 1028 |
| `load` | E | 1991 | 1336 | 1383 | 1939 | 801 | 836 |
| `iconst` | E | 1706 | 1197 | 1217 | 1680 | 712 | 739 |
| `store` | E | 1635 | 1086 | 1125 | 1635 | 1086 | 1125 |
| `jump` | E | 1335 | 698 | 708 | 1335 | 719 | 729 |
| `call` | E | 750 | 273 | 350 | 750 | 260 | 337 |
| `return` | E | 620 | 373 | 377 | 556 | 320 | 323 |
| `icmp` | E | 524 | 278 | 335 | 524 | 208 | 259 |
| `brif` | E | 497 | 280 | 355 | 497 | 258 | 333 |
| `symbol_value` | neither | 405 | 168 | 244 | 405 | 145 | 221 |
| `trap` | E | 355 | 222 | 291 | 304 | 117 | 189 |
| `iadd` | E | 294 | 303 | 303 | 294 | 254 | 261 |
| `imul` | E | 249 | 251 | 245 | 249 | 42 | 33 |
| `ireduce` | E | 110 | 63 | 72 | 110 | 21 | 33 |
| `uextend` | E | 79 | 59 | 62 | 79 | 79 | 82 |
| `br_table` | E | 66 | 36 | 37 | 66 | 36 | 37 |
| `isub` | E | 61 | 45 | 45 | 61 | 48 | 42 |
| `ishl` | E | 43 | 10 | 10 | 43 | 51 | 52 |
| `bor` | E | 41 | 12 | 8 | 41 | 11 | 6 |
| `bxor` | E | 39 | 34 | 38 | 39 | 34 | 38 |
| `band` | E | 23 | 18 | 18 | 23 | 21 | 21 |
| `select` | S\E | 23 | 13 | 13 | 23 | 8 | 8 |
| `umulhi` | E | 16 | 1 | 6 | 16 | 3 | 6 |
| `udiv` | E | 14 | 12 | 12 | 14 | 1 | 1 |
| `ushr` | E | 12 | 12 | 12 | 12 | 19 | 21 |
| `popcnt` | E | 9 | 3 | 3 | 9 | 3 | 3 |
| `call_indirect` | neither | 7 | 7 | 7 | 7 | 7 | 7 |
| `urem` | E | 7 | 7 | 7 | 7 | 1 | 1 |
| `iconcat` | S\E | 5 | 5 | 5 | 5 | 2 | 2 |
| `sextend` | E | 5 | 3 | 5 | 5 | 3 | 5 |
| `rotl` | E | 4 | 7 | 7 | 4 | 7 | 7 |
| `bswap` | S\E | 3 | 3 | 3 | 3 | 3 | 3 |
| `clz` | E | 3 | 3 | 3 | 3 | 3 | 3 |
| `sshr` | E | 3 | 3 | 3 | 3 | 4 | 4 |
| `func_addr` | neither | 2 | 2 | 2 | 2 | 2 | 2 |
| `ineg` | E | 2 | 2 | 2 | 2 | 4 | 4 |
| `sdiv` | E | 2 | 2 | 2 | 2 | 1 | 1 |
| `umax` | S\E | 2 | 2 | 2 | 2 | 2 | 2 |
| `umin` | S\E | 2 | 2 | 2 | 2 | 2 | 2 |
| `bitrev` | S\E | 1 | 1 | 1 | 1 | 1 | 1 |
| `bnot` | E | 1 | 1 | 1 | 1 | 0 | 0 |
| `ctz` | E | 1 | 1 | 1 | 1 | 1 | 1 |
| `rotr` | E | 1 | 10 | 10 | 1 | 10 | 10 |
| `smax` | S\E | 1 | 1 | 1 | 1 | 1 | 1 |
| `smin` | S\E | 1 | 1 | 1 | 1 | 1 | 1 |
| `smulhi` | E | 1 | 1 | 1 | 1 | 2 | 2 |
| `srem` | E | 1 | 1 | 1 | 1 | 1 | 1 |

#### E / S / neither (distinct opcodes / instruction count)

| profile | stage | instructions | E | S\E | neither |
| --- | --- | --- | --- | --- | --- |
| debug | unopt | 17701 | 36 ops / 13769 (77.8%) | 9 ops / 3518 (19.9%) | 3 ops / 414 (2.3%) |
| debug | opt | 17392 | 36 ops / 13524 (77.8%) | 9 ops / 3454 (19.9%) | 3 ops / 414 (2.4%) |
| release | unopt | 10687 | 36 ops / 8744 (81.8%) | 9 ops / 1766 (16.5%) | 3 ops / 177 (1.7%) |
| release | opt | 6533 | 35 ops / 6120 (93.7%) | 9 ops / 259 (4.0%) | 3 ops / 154 (2.4%) |
| release-oc | unopt | 11486 | 36 ops / 9235 (80.4%) | 9 ops / 1998 (17.4%) | 3 ops / 253 (2.2%) |
| release-oc | opt | 7063 | 35 ops / 6573 (93.1%) | 9 ops / 260 (3.7%) | 3 ops / 230 (3.3%) |

#### Non-E opcodes per category (unopt)

| category | debug | release |
| --- | --- | --- |
| (a) arith | `nop`×354, `symbol_value`×40, `select`×4, `bswap`×1, `bitrev`×1, `smin`×1, `smax`×1, `umin`×1 | `nop`×189, `symbol_value`×12, `select`×4, `smin`×1, `smax`×1, `umin`×1, `bswap`×1, `bitrev`×1 |
| (b) slices | `nop`×462, `symbol_value`×55, `bswap`×1, `select`×1 | `nop`×147, `symbol_value`×23, `bswap`×1 |
| (c) structs/enums | `nop`×178, `symbol_value`×8, `select`×2 | `nop`×128, `symbol_value`×3, `select`×2 |
| (d) loops/iters | `nop`×775, `symbol_value`×67, `select`×3, `umin`×1 | `nop`×468, `symbol_value`×26, `select`×2, `umin`×1 |
| (e) Option/Result | `nop`×327, `symbol_value`×19, `select`×5 | `nop`×134, `symbol_value`×17 |
| (f) crypto | `nop`×607, `symbol_value`×114, `bswap`×1 | `nop`×279, `symbol_value`×60, `bswap`×1 |
| (g) u128 | `nop`×143, `symbol_value`×30, `iconcat`×5 | `nop`×41, `iconcat`×5, `symbol_value`×4 |
| (h) generic/dyn | `nop`×244, `symbol_value`×16, `call_indirect`×7, `select`×3, `func_addr`×2 | `nop`×161, `symbol_value`×8, `call_indirect`×7, `func_addr`×2 |
| (i) alloc | `nop`×390, `symbol_value`×56, `select`×5, `umax`×2 | `nop`×191, `symbol_value`×15, `select`×5, `umax`×2 |

#### Functions whose opcodes all lie in a subset (unopt)

| profile | functions | only E | only E + nop | only S |
| --- | --- | --- | --- | --- |
| debug | 454 | 0 | 279 | 298 |
| release | 239 | 0 | 163 | 172 |
| release-oc | 240 | 0 | 136 | 143 |

#### Features: functions using each (unopt)

| feature | debug | release | release-oc |
| --- | --- | --- | --- |
| `br_table` | 50 | 29 | 31 |
| `call_indirect` | 5 | 5 | 5 |
| `cold` blocks | 159 | 67 | 95 |
| `func_addr` | 1 | 1 | 1 |
| `i128` values | 13 | 12 | 12 |
| `iconcat` | 3 | 3 | 3 |
| `nop` | 454 | 239 | 240 |
| `select` | 20 | 10 | 10 |
| `sigN` + `fnN = u0:N sigN` declarations | 304 | 130 | 158 |
| `sret` param/return attribute | 29 | 20 | 20 |
| `symbol_value` | 152 | 63 | 93 |
| `uext` param/return attribute | 56 | 29 | 28 |
| alias `vA -> vB` placed after a use of vA | 17 | 21 | 27 |
| call: cranelift libcall (Memcpy) | 12 | 8 | 8 |
| call: cranelift libcall (Memmove) | 2 | 2 | 2 |
| call: cranelift libcall (Memset) | 3 | 3 | 3 |
| call: external symbol memcmp | 1 | 1 | 1 |
| call: other | 237 | 104 | 105 |
| call: panic path | 118 | 40 | 71 |
| call: runtime symbol __modti3 | 1 | 1 | 1 |
| call: runtime symbol __rust_alloc | 1 | 1 | 1 |
| call: runtime symbol __rust_alloc_zeroed | 1 | 1 | 1 |
| call: runtime symbol __rust_dealloc | 1 | 1 | 1 |
| call: runtime symbol __rust_no_alloc_shim_is_unstable_v2 | 1 | 1 | 1 |
| call: runtime symbol __rust_realloc | 1 | 1 | 1 |
| call: runtime symbol __rust_u128_mulo | 3 | 1 | 3 |
| call: runtime symbol __udivti3 | 1 | 1 | 1 |
| multiple return values | 96 | 32 | 33 |
| stack slots | 267 | 127 | 130 |
| value aliases `vA -> vB` | 398 | 217 | 217 |

#### Instructions mentioning `i128` (unopt)

| opcode | debug | release | release-oc |
| --- | --- | --- | --- |
| `clz` | 1 | 1 | 1 |
| `iadd` | 4 | 1 | 4 |
| `icmp` | 5 | 5 | 5 |
| `imul` | 1 | 1 | 1 |
| `ishl` | 1 | 1 | 1 |
| `load` | 3 | 3 | 3 |
| `popcnt` | 1 | 1 | 1 |
| `sshr` | 1 | 1 | 1 |
| `store` | 1 | 1 | 1 |
| `uextend` | 13 | 8 | 8 |
| `ushr` | 3 | 0 | 3 |

#### debug: detail (unopt)


##### Types (suffixes, signatures, block params)

| item | count |
| --- | --- |
| `i64` | 10495 |
| `i32` | 1997 |
| `i8` | 763 |
| `i128` | 120 |
| `i16` | 97 |


##### Memory ops and flags

| item | count |
| --- | --- |
| `load: notrap` | 1957 |
| `store: notrap` | 1605 |
| `load: notrap aligned` | 30 |
| `store: notrap aligned` | 30 |
| `load: notrap aligned readonly` | 4 |


##### Traps

| item | count |
| --- | --- |
| `trap user1` | 355 |
| `trap user1 after a call` | 256 |
| `trap user1 after block start` | 99 |


##### icmp condition codes

| item | count |
| --- | --- |
| `ult` | 192 |
| `eq` | 144 |
| `ugt` | 93 |
| `ule` | 35 |
| `ne` | 27 |
| `slt` | 17 |
| `uge` | 11 |
| `sgt` | 4 |
| `sge` | 1 |


##### Direct call targets (by kind)

| item | count |
| --- | --- |
| `Rust fn (colocated)` | 451 |
| `panic path` | 255 |
| `cranelift libcall (Memcpy)` | 14 |
| `Rust fn (upstream)` | 8 |
| `runtime symbol __rust_u128_mulo` | 7 |
| `cranelift libcall (Memset)` | 4 |
| `cranelift libcall (Memmove)` | 2 |
| `runtime symbol __rust_no_alloc_shim_is_unstable_v2` | 2 |
| `external symbol memcmp` | 1 |
| `runtime symbol __udivti3` | 1 |
| `runtime symbol __modti3` | 1 |
| `runtime symbol __rust_realloc` | 1 |
| `runtime symbol __rust_dealloc` | 1 |
| `runtime symbol __rust_alloc_zeroed` | 1 |
| `runtime symbol __rust_alloc` | 1 |


##### Calling conventions (function + sigN)

| item | count |
| --- | --- |
| `system_v` | 1213 |


##### ABI attributes on params/returns

| item | count |
| --- | --- |
| `uext` | 155 |
| `sret` | 52 |


##### Global value declarations

| item | count |
| --- | --- |
| `symbol colocated userextnameN ; allocN` | 401 |
| `symbol colocated userextnameN ; vtable` | 4 |


##### Stack slots

873 slots in 267 of 454 functions; kinds {'explicit_slot': 873}; aligns {0: 60, 2: 4, 4: 133, 8: 676}; largest 256 bytes; sizes {1: 16, 2: 27, 4: 37, 8: 410, 9: 1, 16: 344, 24: 17, 32: 9, 40: 3, 48: 3, 64: 4, 256: 2}


#### release: detail (unopt)


##### Types (suffixes, signatures, block params)

| item | count |
| --- | --- |
| `i64` | 6156 |
| `i32` | 1188 |
| `i8` | 514 |
| `i128` | 69 |
| `i16` | 48 |


##### Memory ops and flags

| item | count |
| --- | --- |
| `load: notrap` | 1311 |
| `store: notrap` | 1065 |
| `load: notrap aligned` | 21 |
| `store: notrap aligned` | 21 |
| `load: notrap aligned readonly` | 4 |


##### Traps

| item | count |
| --- | --- |
| `trap user1` | 222 |
| `trap user1 after block start` | 119 |
| `trap user1 after a call` | 103 |


##### icmp condition codes

| item | count |
| --- | --- |
| `eq` | 95 |
| `ult` | 82 |
| `ugt` | 47 |
| `ule` | 30 |
| `slt` | 10 |
| `uge` | 6 |
| `ne` | 6 |
| `sge` | 1 |
| `sgt` | 1 |


##### Direct call targets (by kind)

| item | count |
| --- | --- |
| `Rust fn (colocated)` | 138 |
| `panic path` | 101 |
| `cranelift libcall (Memcpy)` | 10 |
| `Rust fn (upstream)` | 8 |
| `cranelift libcall (Memset)` | 4 |
| `cranelift libcall (Memmove)` | 2 |
| `runtime symbol __rust_no_alloc_shim_is_unstable_v2` | 2 |
| `external symbol memcmp` | 1 |
| `runtime symbol __rust_u128_mulo` | 1 |
| `runtime symbol __udivti3` | 1 |
| `runtime symbol __modti3` | 1 |
| `runtime symbol __rust_realloc` | 1 |
| `runtime symbol __rust_dealloc` | 1 |
| `runtime symbol __rust_alloc_zeroed` | 1 |
| `runtime symbol __rust_alloc` | 1 |


##### Calling conventions (function + sigN)

| item | count |
| --- | --- |
| `system_v` | 521 |


##### ABI attributes on params/returns

| item | count |
| --- | --- |
| `uext` | 59 |
| `sret` | 33 |


##### Global value declarations

| item | count |
| --- | --- |
| `symbol colocated userextnameN ; allocN` | 164 |
| `symbol colocated userextnameN ; vtable` | 4 |


##### Stack slots

540 slots in 127 of 239 functions; kinds {'explicit_slot': 540}; aligns {0: 43, 2: 1, 4: 73, 8: 423}; largest 256 bytes; sizes {1: 11, 2: 22, 4: 25, 8: 261, 9: 1, 16: 189, 24: 16, 32: 7, 40: 2, 48: 1, 64: 3, 256: 2}


### Extra directories: core, alloc

#### Size (unopt CLIF)

| profile | functions | of which the crate's own items | instructions | blocks | cold blocks |
| --- | --- | --- | --- | --- | --- |
| core | 1237 | 1237 | 100471 | 13147 | 1142 |
| alloc | 338 | 237 | 25187 | 3154 | 190 |

#### Opcode histogram (all functions)

| opcode | class | core unopt | alloc unopt | core opt | alloc opt |
| --- | --- | --- | --- | --- | --- |
| `stack_addr` | E | 21278 | 6616 | 9968 | 3171 |
| `nop` | S\E | 14840 | 3215 | 1235 | 337 |
| `load` | E | 13730 | 4347 | 8190 | 2695 |
| `store` | E | 11915 | 3538 | 11905 | 3532 |
| `iconst` | E | 10756 | 1832 | 7021 | 970 |
| `jump` | E | 6378 | 1538 | 6453 | 1556 |
| `icmp` | E | 3122 | 567 | 2247 | 406 |
| `call` | E | 2920 | 593 | 2860 | 576 |
| `brif` | E | 2831 | 457 | 2686 | 423 |
| `symbol_value` | neither | 2057 | 235 | 1883 | 199 |
| `iadd` | E | 1992 | 294 | 1882 | 245 |
| `return` | E | 1856 | 502 | 1618 | 424 |
| `trap` | E | 1608 | 511 | 1060 | 164 |
| `imul` | E | 1297 | 203 | 109 | 13 |
| `uextend` | E | 625 | 66 | 1045 | 216 |
| `ireduce` | E | 618 | 153 | 196 | 51 |
| `isub` | E | 510 | 89 | 616 | 62 |
| `br_table` | E | 474 | 146 | 471 | 145 |
| `band` | E | 283 | 50 | 393 | 50 |
| `ishl` | E | 201 | 26 | 246 | 21 |
| `bor` | E | 156 | 33 | 61 | 23 |
| `select` | S\E | 149 | 86 | 84 | 20 |
| `ushr` | E | 118 | 10 | 237 | 23 |
| `func_addr` | neither | 116 | 22 | 116 | 22 |
| `udiv` | E | 116 | 26 | 14 | 2 |
| `sextend` | E | 79 | 0 | 63 | 0 |
| `iconcat` | S\E | 74 | 0 | 2 | 0 |
| `urem` | E | 74 | 7 | 15 | 0 |
| `call_indirect` | neither | 52 | 5 | 52 | 5 |
| `atomic_load` | S\E | 33 | 0 | 33 | 0 |
| `ineg` | E | 29 | 6 | 43 | 6 |
| `bswap` | S\E | 26 | 1 | 26 | 1 |
| `bxor` | E | 20 | 1 | 15 | 1 |
| `bitcast` | S\E | 19 | 0 | 19 | 0 |
| `bnot` | E | 16 | 5 | 13 | 0 |
| `clz` | E | 13 | 0 | 13 | 0 |
| `fcmp` | neither | 9 | 0 | 9 | 0 |
| `umulhi` | E | 9 | 3 | 41 | 3 |
| `umax` | S\E | 8 | 2 | 14 | 2 |
| `f16const` | neither | 7 | 0 | 7 | 0 |
| `f32const` | neither | 7 | 0 | 7 | 0 |
| `f64const` | neither | 7 | 0 | 7 | 0 |
| `sshr` | E | 6 | 0 | 8 | 0 |
| `umin` | S\E | 6 | 0 | 7 | 0 |
| `ctz` | E | 5 | 2 | 1 | 0 |
| `atomic_store` | S\E | 3 | 0 | 3 | 0 |
| `fcvt_from_uint` | neither | 3 | 0 | 3 | 0 |
| `fdiv` | neither | 3 | 0 | 3 | 0 |
| `fmul` | neither | 3 | 0 | 3 | 0 |
| `isplit` | S\E | 3 | 0 | 3 | 0 |
| `popcnt` | E | 3 | 0 | 3 | 0 |
| `fabs` | neither | 2 | 0 | 2 | 0 |
| `fneg` | neither | 2 | 0 | 2 | 0 |
| `rotl` | E | 2 | 0 | 2 | 0 |
| `sdiv` | E | 2 | 0 | 0 | 0 |
| `smulhi` | E | 0 | 0 | 2 | 0 |

#### E / S / neither (distinct opcodes / instruction count)

| profile | stage | instructions | E | S\E | neither |
| --- | --- | --- | --- | --- | --- |
| core | unopt | 100471 | 33 ops / 83042 (82.7%) | 10 ops / 15161 (15.1%) | 12 ops / 2268 (2.3%) |
| core | opt | 63017 | 33 ops / 59497 (94.4%) | 10 ops / 1426 (2.3%) | 12 ops / 2094 (3.3%) |
| alloc | unopt | 25187 | 27 ops / 21621 (85.8%) | 4 ops / 3304 (13.1%) | 3 ops / 262 (1.0%) |
| alloc | opt | 15364 | 24 ops / 14778 (96.2%) | 4 ops / 360 (2.3%) | 3 ops / 226 (1.5%) |

#### Functions whose opcodes all lie in a subset (unopt)

| profile | functions | only E | only E + nop | only S |
| --- | --- | --- | --- | --- |
| core | 1237 | 2 | 644 | 704 |
| alloc | 338 | 1 | 186 | 216 |

#### Features: functions using each (unopt)

| feature | core | alloc |
| --- | --- | --- |
| `br_table` | 257 | 90 |
| `call_indirect` | 34 | 4 |
| `cold` blocks | 462 | 121 |
| `func_addr` | 38 | 14 |
| `i128` values | 29 | 0 |
| `iconcat` | 16 | 0 |
| `nop` | 1235 | 337 |
| `select` | 111 | 60 |
| `sigN` + `fnN = u0:N sigN` declarations | 1018 | 276 |
| `sret` param/return attribute | 147 | 78 |
| `symbol_value` | 500 | 117 |
| `uext` param/return attribute | 502 | 37 |
| alias `vA -> vB` placed after a use of vA | 152 | 33 |
| call: cranelift libcall (Memcpy) | 97 | 13 |
| call: cranelift libcall (Memmove) | 0 | 3 |
| call: cranelift libcall (Memset) | 27 | 3 |
| call: external symbol memcmp | 4 | 0 |
| call: other | 884 | 254 |
| call: panic path | 215 | 39 |
| call: runtime symbol __extendhfsf2 | 3 | 0 |
| call: runtime symbol __rust_alloc | 0 | 1 |
| call: runtime symbol __rust_alloc_error_handler | 0 | 1 |
| call: runtime symbol __rust_alloc_zeroed | 0 | 1 |
| call: runtime symbol __rust_dealloc | 0 | 3 |
| call: runtime symbol __rust_no_alloc_shim_is_unstable_v2 | 0 | 1 |
| call: runtime symbol __rust_realloc | 0 | 2 |
| call: runtime symbol __rust_u128_mulo | 1 | 0 |
| call: runtime symbol __truncsfhf2 | 3 | 0 |
| call: runtime symbol __udivti3 | 7 | 0 |
| call: runtime symbol __umodti3 | 6 | 0 |
| multiple return values | 201 | 77 |
| stack slots | 1044 | 285 |
| value aliases `vA -> vB` | 1046 | 245 |

#### Instructions mentioning `i128` (unopt)

| opcode | core | alloc |
| --- | --- | --- |
| `band` | 3 | 0 |
| `brif` | 5 | 0 |
| `iadd` | 5 | 0 |
| `icmp` | 9 | 0 |
| `imul` | 1 | 0 |
| `isub` | 4 | 0 |
| `load` | 58 | 0 |
| `popcnt` | 1 | 0 |
| `sextend` | 1 | 0 |
| `store` | 9 | 0 |
| `uextend` | 12 | 0 |
| `ushr` | 4 | 0 |

#### core: detail (unopt)


##### Types (suffixes, signatures, block params)

| item | count |
| --- | --- |
| `i64` | 59855 |
| `i8` | 6651 |
| `i32` | 3889 |
| `i16` | 1250 |
| `i128` | 295 |
| `f32` | 125 |
| `f16` | 119 |
| `f64` | 111 |


##### Memory ops and flags

| item | count |
| --- | --- |
| `load: notrap` | 11857 |
| `store: notrap` | 10083 |
| `load: notrap aligned` | 1832 |
| `store: notrap aligned` | 1832 |
| `load: notrap aligned readonly` | 41 |
| `atomic_load: notrap aligned` | 33 |
| `atomic_store: notrap aligned` | 3 |


##### Traps

| item | count |
| --- | --- |
| `trap user1` | 1608 |
| `trap user1 after a call` | 867 |
| `trap user1 after block start` | 741 |


##### icmp condition codes

| item | count |
| --- | --- |
| `ult` | 855 |
| `eq` | 805 |
| `ugt` | 674 |
| `ule` | 312 |
| `uge` | 170 |
| `ne` | 97 |
| `slt` | 76 |
| `sge` | 72 |
| `sle` | 36 |
| `sgt` | 25 |


##### Direct call targets (by kind)

| item | count |
| --- | --- |
| `Rust fn (colocated)` | 1213 |
| `Rust fn (upstream)` | 578 |
| `Rust fn (by symbol)` | 475 |
| `panic path` | 407 |
| `cranelift libcall (Memcpy)` | 175 |
| `cranelift libcall (Memset)` | 28 |
| `runtime symbol __udivti3` | 13 |
| `runtime symbol __extendhfsf2` | 10 |
| `runtime symbol __umodti3` | 9 |
| `runtime symbol __rust_u128_mulo` | 5 |
| `external symbol memcmp` | 4 |
| `runtime symbol __truncsfhf2` | 3 |


##### Calling conventions (function + sigN)

| item | count |
| --- | --- |
| `system_v` | 4325 |


##### ABI attributes on params/returns

| item | count |
| --- | --- |
| `uext` | 1590 |
| `sret` | 385 |


##### Global value declarations

| item | count |
| --- | --- |
| `symbol colocated userextnameN ; allocN` | 1941 |
| `symbol colocated userextnameN ; vtable` | 48 |
| `symbol userextnameN ; static item` | 35 |
| `symbol colocated userextnameN ; static item` | 33 |


##### Stack slots

6360 slots in 1044 of 1237 functions; kinds {'explicit_slot': 6360}; aligns {0: 1687, 2: 131, 4: 405, 8: 4105, 16: 32}; largest 1024 bytes; sizes {1: 1387, 2: 135, 3: 6, 4: 260, 5: 19, 6: 13, 8: 1782, 9: 1, 10: 21, 11: 1, 12: 50, 14: 1, 15: 1, 16: 1946, 17: 16, 19: 6, 20: 20, 21: 1, 22: 2, 24: 428, 28: 3, 32: 125, 39: 3, 40: 22, 43: 2, 48: 24, 56: 12, 58: 1, 64: 9, 72: 8, 96: 6, 128: 4, 130: 2, 144: 6, 160: 8, 168: 15, 256: 3, 768: 1, 784: 4, 1024: 6}


#### alloc: detail (unopt)


##### Types (suffixes, signatures, block params)

| item | count |
| --- | --- |
| `i64` | 16006 |
| `i8` | 714 |
| `i32` | 676 |
| `i16` | 271 |


##### Memory ops and flags

| item | count |
| --- | --- |
| `load: notrap` | 3775 |
| `store: notrap` | 2973 |
| `load: notrap aligned` | 565 |
| `store: notrap aligned` | 565 |
| `load: notrap aligned readonly` | 7 |


##### Traps

| item | count |
| --- | --- |
| `trap user1` | 511 |
| `trap user1 after block start` | 422 |
| `trap user1 after a call` | 89 |


##### icmp condition codes

| item | count |
| --- | --- |
| `eq` | 211 |
| `ugt` | 197 |
| `ule` | 64 |
| `ult` | 61 |
| `uge` | 19 |
| `ne` | 11 |
| `sge` | 2 |
| `slt` | 2 |


##### Direct call targets (by kind)

| item | count |
| --- | --- |
| `Rust fn (colocated)` | 321 |
| `Rust fn (upstream)` | 177 |
| `panic path` | 48 |
| `Rust fn (by symbol)` | 16 |
| `cranelift libcall (Memcpy)` | 14 |
| `runtime symbol __rust_dealloc` | 4 |
| `cranelift libcall (Memset)` | 3 |
| `cranelift libcall (Memmove)` | 3 |
| `runtime symbol __rust_no_alloc_shim_is_unstable_v2` | 2 |
| `runtime symbol __rust_realloc` | 2 |
| `runtime symbol __rust_alloc_error_handler` | 1 |
| `runtime symbol __rust_alloc_zeroed` | 1 |
| `runtime symbol __rust_alloc` | 1 |


##### Calling conventions (function + sigN)

| item | count |
| --- | --- |
| `system_v` | 958 |


##### ABI attributes on params/returns

| item | count |
| --- | --- |
| `sret` | 179 |
| `uext` | 131 |


##### Global value declarations

| item | count |
| --- | --- |
| `symbol colocated userextnameN ; allocN` | 226 |
| `symbol colocated userextnameN ; vtable` | 9 |


##### Stack slots

1861 slots in 285 of 338 functions; kinds {'explicit_slot': 1861}; aligns {0: 82, 2: 24, 4: 116, 8: 1639}; largest 48 bytes; sizes {1: 61, 2: 22, 3: 3, 4: 70, 8: 668, 12: 6, 16: 800, 24: 181, 32: 34, 40: 11, 48: 5}

## Post-rust-route (branch `agent/rust-route`, after the `agent/optproven-fix` merge)

Final state of the rust route (`docs/research/rust-route.md` has the full log):

| profile | functions | compiled by the Lean backend | unsupported |
| --- | --- | --- | --- |
| debug | 454 | 437 | 17 |
| release | 239 | 227 | 12 |
| release-oc | 240 | 228 | 12 |
| **total** | **933** | **892 (95.6%)** | **41** |

Unsupported reasons (all one cause: **i128**):

| reason | count |
| --- | --- |
| i128 parameter | 31 |
| extend to i128 | 6 |
| i128 return value | 4 |

Everything else the corpus needs — data objects (938 recovered), mem*/panic externs,
sret, `call_indirect`/`func_addr` (dyn dispatch over recovered vtables) — compiles, runs
under `Clif.run`, and agrees natively with Cranelift and rustc/LLVM where the backend
runs it (all flagged unverified in the theorem's scope: outside `E2E.InSubset`).

**i128 semantics are done; i128 code generation is not.** `Clif.run` executes the i128
functions correctly (`iadd.i128`, `load.i128`, `iconcat`, …; `iconst.i128` is rejected by
both readers, so constants come via `iconcat`). The backend rejects them at three gates:
`sigArgs` throws on an i128 parameter, `lowerFunction` on an i128 return value, and
`instData`/`instE` on every i128 opcode. Enabling them needs Cranelift's two-register
`ValueRegs` value model (one i128 value = two vregs, AAPCS64 even/odd register pairs,
pair results from the exported i128-tagged ISLE rules — currently `defaultExcludes`
"i128", and `lowerFunction` throws "multi-register result"), which cuts through the
verified lowering simulation (every value is one vreg today). `smoke.sh` now runs the
`g_u128` corpus functions with rustc/LLVM as the oracle: **103 run lines — Clif.run 101
pass / 0 fail / 2 unsupported (pre-existing missing panic extern), Cranelift-native
agrees 101, Lean backend 88 pass / 13 not-compiled (the u128 functions)**.

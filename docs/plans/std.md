# T3 (#39): std through `cargo fv` (`-Zbuild-std`)

Today the standard library is the prebuilt LLVM build: std, core, alloc, compiler_builtins and
musl libc are code outside the program, and every call into them is an outside call whose
callee contract (`CalleeOk`, `XCallsOk`; docs/contracts/e2e.md) is trusted (TO-PROVE §1.3).
This plan puts std's Rust crates through the same path as any dependency: cg_clif dumps their
CLIF, the Lean backend compiles each function, `--lean-link` places them in the executable's
Lean region. Measured on 2026-10-22 at `8442c331` (main) plus this branch.

## 1. How (step 2, done in this PR: `cargo fv --build-std`)

* `cargo fv … --build-std` runs cargo with `-Zbuild-std=std,panic_unwind` (`panic_abort` with
  `--panic-abort`; cargo adds `test` for test harnesses) in its own target directory (`-std`).
* **Sources.** cg_clif cannot compile 128-bit atomics (`128bit atomics not yet supported`,
  `intrinsics/mod.rs`); core's `impl Debug for AtomicU128` instantiates them, so plain
  `-Zbuild-std` stops in core on aarch64 (`docs/research/rust-clif-survey.md`). cg_clif builds its
  own sysroot from sources with its `patches/*-stdlib-*.patch` applied (0027: the
  `AtomicI128`/`AtomicU128` types are `#[cfg(false)]`). `scripts/build-cg-clif.sh` now prepares
  the same: `target/cg_clif/std-src/library` = the toolchain's `rust-src` + cg_clif's stdlib
  patches of the pinned commit; `cargo fv` points cargo's build-std source root
  (`__CARGO_TESTS_ONLY_SRC_ROOT`) at it (`FV_STD_SRC` overrides). The patch only removes two
  unstable types; a crate that uses them no longer compiles (it cannot run wrong code).
* **compiler_builtins stays on LLVM**: cg_clif rejects its `f128` code (`__lttf2` declared with two
  signatures). `fv-rustc` drops `-Zcodegen-backend` for it, so its libcalls (`__udivti3`, …) stay
  outside code, as musl libc does.
* **Which units are std.** cargo passes `-Zforce-unstable-if-unmarked` to exactly the units it
  builds for `-Zbuild-std`; `fv-rustc` marks those units `std` (and `dep`). The report counts them
  in a third group (`std`, kind `std` in the per-unit rows, `cargo fv: … std N of M (V verified)`),
  with their own unverified/fallback reasons; `FV_SKIP_DEPS=std` etc. keep single std crates on
  plain cg_clif.
* **Executable attribution.** With `--lean-link` the region object holds every unit's Lean code;
  the `exe` line now attributes each Lean function by its symbol to the unit report listing it
  (`Lean … (your crate(s), dependencies, std)`, `Lean in exe per std crate`); compiler_builtins
  counts as prebuilt/LLVM.
* **Large units.** std's single codegen unit has 12607 functions: the `ld -r` of its Lean
  objects exceeded the command-line limit (`Argument list too long`); the inputs now go through a
  response file.

## 2. Measurements (step 1)

`cargo fv test --lean-link [--verified] [--build-std]`, debug profile (as the per-PR gate),
panic=unwind, 16 `lean-backend` jobs.

### examples/fv-demo

| | functions | verified | fallback | Lean in exe (lib test / main test) | outside code in exe |
| --- | --- | --- | --- | --- | --- |
| before (prebuilt std) | 1370 | 1364 | 6 | 903 / 461 | 1661 / 1640 (std, compiler_builtins, musl) |
| `--build-std` | 32447 (members 2089, std 30358) | 32212 (std 30129) | 235 (std 229) | 28568 / 27919 | 604 / 604 (compiler_builtins, musl, crt) + 187 / 186 cg_clif fallbacks |

Per std crate (functions / verified): std 12607 / 12607, test 5374 / 5278, core 3367 / 3270,
proc_macro 2936 / 2922, object 1660 / 1660, alloc 1109 / 1109, gimli 897 / 875, getopts 807 /
807, rustc-demangle 514 / 514, miniz_oxide 303 / 303, memchr 269 / 269, addr2line 143 / 143,
std_detect 121 / 121, hashbrown 94 / 94, panic_unwind 75 / 75, adler2 50 / 50, libc 27 / 27,
rustc-literal-escaper 3 / 3, panic_abort 2 / 2. **99.2 % of std's functions are inside
`E2E.backend_correct_final_cleanup`.** (Survey: §2.3.)

### Fallback reasons in std, ranked (229)

| # | reason | crates | kind |
| --- | --- | --- | --- |
| 90 | `ctlCheck` failed | core 40, test 40, proc_macro 6, gimli 4 | floats: `f32/f64::{abs, classify, to_bits, from_bits, …}` (float values in the control lowering) |
| 39 | `try_call` with f32/f64 parameters or returns | core, test | floats |
| 33 | `type f16` (decode) | core | floats (`f16`) |
| 31 | outside clif-subset-v2 E | core 10, test 10, gimli 7, proc_macro 4 | floats: `float_to_decimal_common_exact::<f32>`, `gimli::read::value::Value::{add, mul, div, …}` on f32/f64, `ParseFloatError` maps |
| 22 + 7 + 4 + 1 + 1 | `fcmp`, `fcvt_from_uint`, `fcvt_to_uint_sat`, `fcvt_from_sint`, `floor` not in the lowering | core, test, gimli | floats |
| 1 | validation budget (`proc_macro::quote::quote`, 4·10⁸ instructions × values) | proc_macro | budget |

So **228 of 229 std fallbacks are floats** (S11, Floats11 / `docs/plans/floats.md`), one is the
validation budget. The other reasons the issue anticipated do not occur in std on this target:

* **SIMD: none.** A census of cg_clif's dumps of std (release, aarch64, `/tmp/StdT3_clifstats.py`
  on 8700 functions; S12 confirmed it with `scripts/simd-scan.py`: 8401 distinct functions) finds
  no vector type: std's NEON paths (memchr, `core::arch`) are not compiled into these crates, and
  cg_clif lowers the portable SIMD intrinsics std uses to scalar code.
* **Inline asm: none** in std's Rust code compiled by cg_clif (no `__inline_asm_*` wrapper in any
  dump). The syscalls are in musl (C).
* **Atomics**: 55 functions with `atomic_rmw`/`atomic_cas` in std (release census), all compiled
  and verified on the single-core model (T2's memory-model statement is separate).
* **Unwinding**: 2140 functions with `try_call` (release census); all verified for their normal
  returns, the exceptional edge by S10's `…_unwind` theorems.
* **i128**: 60 functions (release census), all through the proven legaliser.

### 2.1 The executable: `--lean-link --verified`

With std in the program `P`, `lean-link --verified` rejects both fv-demo test executables:
17 (main test) / 18 (lib test) functions fail the program-level per-function input conditions
of `InScopeP` (`docs/contracts/dead-cleanup.md`):

* `indB:sretRets` (8 / 9): an indirect call of the function can enter (by signature, `indSigB`) a
  function of `P` with more than 8 parameter bytes in registers or with a different number of
  ABI returns (`indRetsB`). With prebuilt std the possible targets were few; with std in `P` the
  `dyn` calls of std/test (`FnOnce` shims, `fmt::Write`) match more functions;
* `callScopeB:blrRegs` (10): a call through a register whose arguments are not all in registers.

Failing functions: std 6, test 11, fv-demo 1 (`_RNxC7fv_demo12Hgl7BS49lQJI`, which passed before:
one of its indirect calls can now reach a std function). Without `--verified` the executables are
written by the bare Lean linker (`Link.DeadCleanup.leanLink`, no compiler theorem) and the tests
pass (§2.2). These are scope conditions of the compiler theorem (stack arguments / indirect calls:
S5 `StackArgsS5`, S-indirect), not std-specific; the fix is either widening `indB`/`callScopeB` or
dropping the failing functions from `P` at link time (§4, slice T3c).

### 2.2 Cost

fv-demo debug with `--build-std`: cargo + cg_clif + `lean-backend` for all 32447 functions: about
8 minutes (16 jobs). `lake exe lean-link` on the 28k-function region: **2 h 13 min / 2 h 26 min**
per executable (before: seconds for 461/903 functions); the binary check (`link-check`) on it:
over 1.5 h. Both are linear-time in intent; at this size the program-level checks that quantify
over `P` per function (`indB`, `callScopeB`, `mayB`) dominate (quadratic). Slice T3d.

### 2.3 Survey

`examples/survey` (9 crates, 3179 functions, all verified before): see the table in the PR body /
`docs/USAGE.md` "Examples and results".

### 2.4 Outside contracts that become proven

Outside callees of the Lean region (names `P` calls but does not define), fv-demo main test:

| | outside callees | of which Rust (std/core/alloc/test) | C / libcalls |
| --- | --- | --- | --- |
| before | 54 (lib test 108) | 49 (core 29, std 7, alloc 7, `__rust_*` 4, test 1, own fallbacks 2) | 4: `_Unwind_Resume`, `__udivti3`, `__umodti3`, `__rust_u128_mulo` (lib test also `memcmp`) |
| `--build-std` | 207 (208) | 40: float fallbacks of core (18) and test (14), gimli 1, own fallbacks 2, allocator shim `__rust_{alloc,dealloc,realloc,alloc_zeroed,no_alloc_shim_is_unstable_v2}` 5 | 167: musl's API (`malloc`/`calloc`/`free`/`posix_memalign`, `write`/`read`/`open`/…, `pthread_*`, `mmap`, `abort`, `exit`, `getenv`, sockets, …), libunwind (`_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_GetIP`, …, `dl_iterate_phdr`), compiler_builtins (`__udivti3`, `__umodti3`, `__rust_u128_mulo`) |

The number of outside callees grows, because the boundary moves down: before it was std's Rust API
(`core::fmt`, `core::panicking::assert_failed`, `alloc::raw_vec::…::grow_amortized`,
`std::thread::Thread::new`, `std::io::Stderr::write`, …), whose behaviour (and ABI conformance)
the theorems assumed; with `--build-std` those functions are compiled and verified like the
program, and the boundary is libc's C API and the unwinder. Per area:

* **allocator**: `alloc::raw_vec`, `Vec`, `Box`, `Arc` drop paths and `std::alloc::System`'s
  `__rdl_alloc` are verified; outside remain the allocator shim symbols `__rust_alloc` & co. (the
  shim rustc synthesises in the final crate; cg_clif writes no dump for it — slice T3b) and musl's
  `malloc`/`free`/`realloc`/`posix_memalign`;
* **I/O**: `std::io` (`Write` for `Stderr`/`Stdout`, `fmt::Write` adapters), `core::fmt` (all
  integer formatting, `Formatter`, builders) verified; outside: musl `write`/`writev`/`read`/…;
* **panics**: `core::panicking::*`, `std::panicking::{begin_panic_handler, rust_panic_with_hook}`,
  `panic_unwind::__rust_start_panic` verified (the exceptional edges by S10); outside: libunwind
  (`_Unwind_RaiseException` …) and the personality model, already trusted by design;
* **startup**: `std::rt::lang_start_internal`, thread/TLS setup, argument parsing (`getopts` in
  the test harness) verified; outside: musl's `_start_c`/`__libc_start_main`, crt objects, and
  the TLS hook (T1).

The float fallbacks (32 core/test functions in the region's outside callees) are the remaining
Rust std code outside; S11 removes them.

## 3. musl stays trusted

musl is C; nothing in this repository turns C into CLIF (cg_clif is a rustc backend), so musl
cannot go through `cargo fv`. Alternatives considered:

* a Rust libc (e.g. relibc) compiled with `--build-std`: its syscall layer is inline asm (`svc
  #0`), which cg_clif lowers to `global_asm!` wrappers outside CLIF; it would need an inline-asm
  slice (a verified `svc` wrapper with the Linux syscall contract as the new boundary) and porting
  std's `unix` backend to it. Not reachable now;
* a C frontend producing CLIF: none exists in the pinned toolchain.

So the boundary after T3 is musl's C API + libunwind + compiler_builtins' libcalls, with their
contracts trusted (TO-PROVE §1.3 is updated accordingly).

## 4. Slices

* **T3a (this PR)**: `--build-std` wiring, std group in the report, attribution, response file,
  this plan, docs.
* **T3b**: the allocator shim (`__rust_alloc` & co.): emit/dump it through cg_clif so it is in
  `P` (a forwarding function to `__rdl_alloc`); then the allocator boundary is exactly musl's
  `malloc` family.
* **T3c**: `--verified` with `--build-std`: per-executable exclusion of the functions failing the
  program-level conditions (rebuild the region without them; they keep cg_clif's weak copy), or
  widen `indB`/`callScopeB` (stack arguments in indirect calls; with S5).
* **T3d**: `lean-link`/`link-check` scaling to ~30k functions (index the program-level checks by
  signature / callee instead of scanning `P` per function).
* **T3e**: release-profile and survey/examples/deps measurements with `--build-std` in the
  per-PR gate list once T3c/T3d make it affordable.
* Floats in std: S11 (Floats11).

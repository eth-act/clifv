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
written by the bare Lean linker (`Link.DeadCleanup.leanLink`, no compiler theorem); run under
qemu they pass the same tests as before (lib test 21 passed, main test 0 tests, `ok`), with
28568 / 27919 Lean-compiled functions, all of std but its float fallbacks. These are scope
conditions of the compiler theorem (indirect calls, stack arguments: S5), not std-specific.

**T3c (done): per-executable exclusion.** On an input outside `InScopeIn`/`SrcScopeB`,
`lean-link --verified` now also prints the functions failing a *per-function* condition
(`--verified: exclude: …`: `srcFails`, `fnScopeInFails`, `scopeFails`), when the program-wide
conditions (`helperFreeB`, distinct names, `addrSlotsInputB`) hold. `cargo fv` then rebuilds the
region without them (`pipeline::lean_variant`: the unit's Lean object again from its
per-function objects, `lean-funcs.txt`, minus the excluded ones, cached per exclusion set), so
their symbols bind to cg_clif's weak copies (outside code, like a fallback's), relinks and runs
`lean-link` again (at most 4 rounds; every condition is decided again on the new input, nothing
is assumed from the previous round). Leaving a function out of `P` only drops conjuncts of the
other functions' conditions (each quantifies over `P`'s functions), so one round sufficed on
fv-demo. The exclusion list is `target/fv/<mode>/tmp/exclude-<tag>.txt`; `cargo fv link-proof`
leaves those functions out of the binary check's bundle; the `lean-link` line of the report
names their number. fv-demo with `--build-std --lean-link --verified`: **both executables written
by `Link.DeadCleanup.compileExe` and covered by `compileExe_correct{,_peak,_source,_source_peak}`
(input in `InScopeIn`)**, 28550 (lib test, 18 excluded) / 27902 (main test, 17 excluded) functions
in the region; under qemu lib test 21 passed, main test `ok`. The exceptional edges of one std
function (`gimli::read::abbrev::…::parse`) stayed uncovered (`unwOkB: …: lastCallsOk`, S10): its
last block ends in a plain `blr x8` (`memcpy` through the GOT) followed by `mov x0, x19`, and a
`try_call` elsewhere is also a `blr x8`; `lastCallsOk` only told such calls apart by a following
`udf`. It now also accepts a following register move (`afterLine?`, `FV/E2E/RegLevelCallSite.lean`;
`q_callSite_last` unchanged): `lean-backend` reports that function inside
`backend_correct_final_cleanup_unwind`. Widening `indB`/`callScopeB` (S5) would shrink the
exclusion list; it is not needed for coverage of the rest.

### 2.2 Cost

fv-demo debug with `--build-std`: cargo + cg_clif + `lean-backend` for all 32447 functions: about
8 minutes (16 jobs). `lake exe lean-link` on the 28k-function region: **2 h 13 min / 2 h 26 min**
per executable before T3d (before `--build-std`: seconds for 461/903 functions); the binary check
(`link-check`) on the first executable was stopped after 2.5 h.

**T3d, lean-link (done):** profiled with gdb stack sampling (`perf` unavailable): the time was in
list scans repeated per element, not in the compiler. Fixed, statements unchanged:

* `InScopeIn`/`InScopeP`'s program-level conditions looked a name up in `P` (`P.func?`, a scan of
  28k functions) at every declaration and call site, and in the image's symbols (`List.lookup`)
  for every pair (function with indirect calls, function of `P`) in `indB`/`indSiteB`.
  `Link.inScopePar`/`inScopeInPar` now evaluate `progScopeFastB`/`progScopeInFastB`
  (FV/E2E/LinkScopeFast.lean): the same conditions with `P`'s functions in a hash map
  (`funcMap`, `funcMap_get : (funcMap P)[n]? = P.func? n`) and the symbols in one
  (`assocMap_get : (assocMap l)[n]? = l.lookup n`); `progScopeFastB_eq`, `progScopeInFastB_eq`,
  `inScopePar_eq`, `inScopeInPar_eq` (axioms: propext, Classical.choice, Quot.sound);
* the frontend bundle (`Front.assemble`/`buildSpec`): `reachSet` (data closure) made
  `ds.length + 1` passes over all data objects (now a worklist, linear in the relocations);
  `scopingB`/`localIds`/`globalNames` tested membership in each unit's `localNames` list (now a
  hash set per unit, `PCgu.localIdents`/`globalIdents`, `scopingB_sound` unchanged);
  `buildSpec` rebuilt the whole symbol table per outside name (now once); `sizesFor`/`linkAddrs`
  used `List.lookup` per name (now `firstMap`).

`lean-link --dead-cleanup --verified` on the lib test's region (28550 functions, 25868 data
objects): **2 h 26 min → 11 min 55 s** (715 s, max RSS 2.3 GB; run while two `link-check`s used
other cores). Without `--lean-link` (the default merge mode) and with `--no-binary-check`,
`--build-std` costs minutes (survey below: 6 min). `link-check --dead-cleanup --prune` (the
per-executable binary check, `okB`) on the same region: hash maps (`LinkCheckFast`,
`BinCheckFast`), one task per function for the pipelines, the routing recovery and the static
checks (`Link.parMap`), and the symbol map of the stack bound built once (`budMapFast`; inside the
edge lambda it was rebuilt per candidate edge of every indirect caller): did not finish in 67 min
before (killed) → **5 min 19 s** (static checks 52 s, `okB` 166 s, binary checks 5 s, code map
20 s, stack bound 65 s; max RSS 1.2 GB; okB/binary/code map ok, 0 dropped). Output on the fv-demo
and survey non-std bundles (22 executables, with and without `--dead-cleanup --prune`) equals
main's up to the timing lines.

### 2.3 Survey

`examples/survey` (9 crates, 18 test executables), `cargo fv test --no-binary-check`:

| | members (functions / verified) | std (functions / verified / unverified / fallback) | Lean in a test executable | tests |
| --- | --- | --- | --- | --- |
| before | 3179 / 3179 | — (prebuilt: 1627–1644 functions per executable) | 27–493 | 27 `ok` |
| `--build-std` | 4196 / 4196 | 30358 / 30129 / 32 / 197 | 27262–27878 (std 27229 in each) | 27 `ok` |

The members have more functions with `--build-std` (probably generic instances no longer shared
from the prebuilt rlibs [inference]); all are verified. In the merge mode the 32 outside-E float
functions of std run Lean code unverified (under `--lean-link` they keep cg_clif's code).

With `--build-std --lean-link --verified` (T3e, after T3b/T3d; `examples/compare.sh`, debug,
`FV_JOBS=4`/`2` on a loaded machine):

| | members + deps (functions / verified / fallback) | std (functions / verified / fallback) | Lean in a test executable | excluded per executable (T3c) | binary check | tests |
| --- | --- | --- | --- | --- | --- | --- |
| survey | 4268 / 4268 / 0 | 30358 / 30129 / 229 | 27222–27838 (std 27001–27006) | 17 (each of 18) | 18 / 18 verified (`Link.DeadCleanup.compileExe_correct*`) | SAME, 53 `ok` |
| examples/deps | 31024 / 30821 / 203 | 30358 / 30129 / 229 | 47043–56672 (std 20920–26940) | 17, 17, 17, 6 | 4 / 4 verified | SAME, 16 `ok` |

Wall time: survey 3 h 39 min (13153 s, `FV_JOBS=4`), deps 1 h 41 min (6058 s, `FV_JOBS=2`, cargo
cached from a run killed by systemd-oomd); both under memory pressure from other jobs. With the
default `FV_JOBS` (all cores) both were killed by `memcap` at 24G.

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

### 3.1 The outside-contract set that remains

Measured on fv-demo's lib test with `--build-std --lean-link --verified` (T3c): the undefined
symbols of the Lean region (`llvm-nm -u` of its `*.fvlean.rcgu.o`) that are not Rust symbols:
**170 names**. Each call of one is an outside call whose callee contract is trusted: the AAPCS64
callee contract `CalleeOk`/`CalleeOkG` (returns to the link register with `sp`, the callee-saved
registers and the caller's frame kept, results in x0.., only its dead stack below `sp` clobbered)
and the extern's semantics `XCallsOk`/`XCallsIndOk` (`env.extern n`, the memory relation kept;
`XTrapsOk` where it does not return), docs/contracts/e2e.md. By area:

* memory allocation (5): `calloc`, `free`, `malloc`, `posix_memalign`, `realloc`;
* memory/string primitives (6; cg_clif also calls the first four for `copy`/`write_bytes`/`compare_bytes`): `memcmp`, `memcpy`, `memmove`, `memset`, `strlen`, `strnlen`;
* compiler_builtins libcalls, LLVM-built (3): `__rust_u128_mulo`, `__udivti3`, `__umodti3`;
* libunwind (its model is trusted by design, S10f) and its lookup (15): `dl_iterate_phdr`, `_Unwind_Backtrace`, `_Unwind_DeleteException`, `_Unwind_FindEnclosingFunction`, `_Unwind_GetCFA`, `_Unwind_GetDataRelBase`, `_Unwind_GetIP`, `_Unwind_GetIPInfo`, `_Unwind_GetLanguageSpecificData`, `_Unwind_GetRegionStart`, `_Unwind_GetTextRelBase`, `_Unwind_RaiseException`, `_Unwind_Resume`, `_Unwind_SetGR`, `_Unwind_SetIP`;
* threads and TLS keys (16; the single-thread model of T2 applies): `pthread_attr_destroy`, `pthread_attr_getguardsize`, `pthread_attr_getstack`, `pthread_attr_init`, `pthread_attr_setstacksize`, `pthread_create`, `pthread_detach`, `pthread_getattr_np`, `pthread_join`, `pthread_key_create`, `pthread_key_delete`, `pthread_self`, `pthread_setname_np`, `pthread_setspecific`, `sched_getaffinity`, `sched_yield`;
* process control and spawning (28): `abort`, `chroot`, `execvp`, `_exit`, `exit`, `fork`, `getpid`, `getppid`, `kill`, `killpg`, `pause`, `posix_spawnattr_destroy`, `posix_spawnattr_init`, `posix_spawnattr_setflags`, `posix_spawnattr_setpgroup`, `posix_spawnattr_setsigdefault`, `posix_spawn_file_actions_addchdir_np`, `posix_spawn_file_actions_adddup2`, `posix_spawn_file_actions_destroy`, `posix_spawn_file_actions_init`, `posix_spawnp`, `setgid`, `setgroups`, `setpgid`, `setsid`, `setuid`, `waitid`, `waitpid`;
* file system and file descriptors (55): `chdir`, `chmod`, `chown`, `close`, `closedir`, `dirfd`, `dup`, `dup2`, `fchmod`, `fchmodat`, `fchown`, `fcntl`, `fdatasync`, `fdopendir`, `flock`, `fstat`, `fsync`, `ftruncate`, `futimens`, `getcwd`, `ioctl`, `isatty`, `lchown`, `linkat`, `lseek`, `lstat`, `mkdir`, `mkdirat`, `mkfifo`, `open`, `openat`, `opendir`, `pipe2`, `poll`, `pread`, `preadv`, `pwrite`, `pwritev`, `read`, `readdir`, `readlink`, `readv`, `realpath`, `rename`, `renameat`, `rmdir`, `sendfile`, `splice`, `stat`, `symlink`, `unlink`, `unlinkat`, `utimensat`, `write`, `writev`;
* sockets and name resolution (20): `accept4`, `bind`, `connect`, `freeaddrinfo`, `gai_strerror`, `getaddrinfo`, `getpeername`, `getsockname`, `getsockopt`, `listen`, `recv`, `recvfrom`, `recvmsg`, `send`, `sendmsg`, `sendto`, `setsockopt`, `shutdown`, `socket`, `socketpair`;
* signals (5): `sigaction`, `sigaddset`, `sigaltstack`, `sigemptyset`, `signal`;
* memory mapping (3): `mmap`, `mprotect`, `munmap`;
* environment, users, time, system (14; `environ` is data): `clock_gettime`, `clock_nanosleep`, `environ`, `__errno_location`, `getauxval`, `getenv`, `gethostname`, `getpwuid_r`, `getuid`, `setenv`, `syscall`, `sysconf`, `unsetenv`, `__xpg_strerror_r`.

Besides those: std's optional libc symbols, looked up as weak data
(`__rust_extern_with_linkage_*`: `copy_file_range`, `getrandom`, `gettid`, `pidfd_getpid`,
`pidfd_spawnp`, `__cxa_thread_atexit_impl`, `__dso_handle`; std checks them for null before a
call); musl's startup (`_start`/`_start_c`, `__libc_start_main`, the crt objects, which call
`main`, i.e. enter the program, and run before it) and the TLS hook (`TlsOk`, T1); the remaining
Rust code outside the region: `__rust_no_alloc_shim_is_unstable_v2` (empty; deliberately not
dumped by T3b, see §4), std's float fallbacks (S11), and the per-executable exclusions of T3c
(17 / 18 functions on fv-demo, cg_clif's code). Since T3b the allocator shim
`__rust_{alloc,dealloc,realloc,alloc_zeroed}` is in the region (verified forwarding functions to
`__rdl_*`). The list is what the region *references*; a given run calls a subset.

## 4. Slices

* **T3a (done, #396)**: `--build-std` wiring, std group in the report, attribution, response file,
  this plan, docs.
* **T3b (done)**: the patched cg_clif dumps the allocator shim wrappers `__rust_alloc`,
  `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`; cargo-fv picks them up unchanged.
  fv-demo `--build-std --lean-link --verified`: region 28550 → 28554 functions (lib test), 27902 →
  27906 (main test), exclusions unchanged (18 / 17), all 8 wrappers verified; qemu: lib test 21
  passed, main test ok. The empty `__rust_no_alloc_shim_is_unstable_v2` is not dumped: for a file
  without `try_call`, `lean-backend` lowers with `Stock.Scalar`, which drops the empty `args []` of
  a parameterless function while `lean-link`'s lowering keeps it, so the recorded allocation does
  not apply, `lean-link` falls back to the spill allocation (4 → 42 words) and placement fails
  (`placeOkB`); reported on #140. The allocator boundary is now musl's `malloc` family.
* **T3c (done)**: `--verified` with `--build-std`: per-executable exclusion of the functions
  failing a per-function condition (§2.1). Widening `indB`/`callScopeB` (stack arguments in
  indirect calls; with S5) would shrink the exclusions.
* **T3d (done)**: `lean-link` and `link-check` scaling to ~30k functions (hash maps, §2.2:
  `lean-link` 2 h 26 min → 12 min, `link-check` >67 min → 5 min 19 s).
* **T3e**: release-profile and survey/examples/deps measurements with `--build-std` in the
  per-PR gate list once T3c/T3d make it affordable.
* Floats in std: S11 (Floats11).

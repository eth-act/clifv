# `cargo fv`: building Rust crates with the Lean backend

`cargo fv build|run|test` works like the corresponding cargo command, but the functions of
your crate are compiled by the all-Lean CLIF → AArch64 backend of this repository. The Rust
frontend is rustc_codegen_cranelift (cg_clif): it lowers Rust to CLIF, and for every function
of a workspace member the Lean backend compiles that CLIF again. The Lean code replaces
cg_clif's code for that function. Functions the Lean backend cannot compile keep cg_clif's
code (**fallback**), so the build never fails because of the Lean backend. After each build,
`target/fv-report.json` and a summary on stderr list every function as one of:

* **verified**: compiled by the Lean backend and inside the end-to-end theorem
  (`E2E.backend_correct_final`, or `E2E.backend_correct_opt_proven` with `--opt-proven-only`;
  for `i128` functions `E2E.backend_correct_legal`, without `--opt`);
* **compiled, unverified**: compiled by the Lean backend but outside the theorem (the reason
  is given, e.g. an indirect call, or an `i128` function under `--opt`), or over the
  validation budget (see *What is verified, and what is not*);
* **fallback**: cg_clif's code (the reason is given).

```
$ cargo fv test
   Compiling fv-demo v0.1.0 (…/examples/fv-demo)
cargo fv report — aarch64-unknown-linux-musl debug profile, mode plain
  verified = compiled by the Lean backend and inside E2E.backend_correct_final
  package              kind  crate root             functions  verified unverified  fallback   Lean in exe
  fv-demo              lib   src/lib.rs                   …
  …
cargo fv: 968 of 975 functions compiled by the Lean backend (717 verified); report: …/target/fv-report.json
     Running unittests src/lib.rs (…)
test tests::arithmetic ... ok
…
```

## Install

This host is x86_64 Linux. The binaries are static `aarch64-unknown-linux-musl` executables,
and they run under `qemu-aarch64-static`.

1. The pinned nightly with cg_clif and the musl target:
   ```
   rustup toolchain install nightly-2026-09-26 \
       --component rustc-codegen-cranelift-preview --target aarch64-unknown-linux-musl
   ```
2. `qemu-aarch64-static` on `PATH`. With `--panic-abort`, `cargo test` of a `should_panic`
   test needs the binfmt_misc registration too: the test harness then runs the test in a child
   process (`/proc/sys/fs/binfmt_misc/qemu-aarch64`, from the `qemu-user-static` package).
3. LLVM 18 binutils (`/usr/lib/llvm-18/bin/llvm-objcopy`, `llvm-ar`) and `python3`.
4. The repository's tools, built once from the repository root:
   ```
   FV_MEMCAP=16G scripts/memcap.sh lake build lean-backend
   cd rust && FV_MEMCAP=16G ../scripts/memcap.sh cargo build --release \
       -p cargo-fv -p clif-data-export -p lean-regalloc
   export PATH=$PWD/target/release:$PATH      # cargo-fv and fv-rustc
   ```
   `cargo-fv` finds `lean-backend`, `clif-data-export`, `lean-regalloc` and
   `scripts/rust-clif/normalize.py` through the checkout it was built from (`FV_ROOT`
   overrides this). `cargo install --path rust/crates/cargo-fv` also works: it installs both
   binaries, and they still use that checkout.
5. Recommended for panic=unwind (the default): cg_clif with landing pads, built once from the
   nightly's own sources (network access, the `rustc-dev` component, about 40 s):
   ```
   FV_MEMCAP=16G scripts/memcap.sh scripts/build-cg-clif-unwind.sh
   ```
   It writes `target/cg_clif-unwind/librustc_codegen_cranelift.so` in the checkout, which
   `cargo fv` then uses (see *Panics and unwinding*). Without it, `cargo fv` uses the shipped
   cg_clif, which has no landing pads, and prints a note.

## Usage

```
cargo fv build [--release] [cargo options]
cargo fv run   [--release] [cargo options] [-- program args]
cargo fv test  [--release] [cargo options] [-- test-harness args]
cargo fv report [--functions] [--json]
```

Options of `cargo fv` (all other options go to cargo unchanged):

| option | effect |
|---|---|
| `--opt` | run the Lean mid-end with every rule. Most simplify rules are unproven, so no function is reported verified. |
| `--opt-proven-only` | run the Lean mid-end with the proven rule set; verified = inside `E2E.backend_correct_opt_proven` |
| `--no-fallback` | fail (exit 1, before running anything) unless every function of every workspace member runs Lean code |
| `--trap-replaced` | overwrite cg_clif's code of every Lean-compiled function with `udf` traps (see *Checking that the Lean code runs*) |
| `--keep-temps` | keep the per-codegen-unit work directories (`target/fv/<mode>/tmp/`) |
| `--panic-abort` | build with `-Cpanic=abort -Zpanic-abort-tests` (the pre-unwinding behaviour; the shipped cg_clif; own target directory) |

`cargo fv report` prints the summary of the last build again. `--functions` lists every
function with its status and reason, and `--json` prints `target/fv-report.json`.

Environment variables:

| variable | effect |
|---|---|
| `FV_JOBS` | parallel `lean-backend` processes per codegen unit (default: number of CPUs) |
| `FV_SKIP=pat,…` / `FV_ONLY=pat,…` | debugging: functions whose symbol or Rust path contains a pattern fall back / only those are compiled |
| `FV_TOOLCHAIN` | the nightly (default `nightly-2026-09-26`) |
| `FV_CG_CLIF` | the codegen backend: a cg_clif `.so`, or `cranelift` for the shipped one (default: `target/cg_clif-unwind/librustc_codegen_cranelift.so` of the checkout if it exists and panic=unwind, else `cranelift`) |
| `FV_ROOT` | the repository checkout with the tools |
| `FV_OBJCOPY`, `FV_AR`, `FV_RUST_LLD`, `FV_PYTHON` | tool paths |
| `CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER` | the runner (default `qemu-aarch64-static`) |

Per package, `Cargo.toml` can keep functions on cg_clif:

```toml
[package.metadata.fv]
skip = ["interop::cg_clif_"]   # substrings of the symbol or the Rust path
```

Artifacts are in `target/fv/<mode>/aarch64-unknown-linux-musl/<profile>/…`, where `<mode>` is
`plain`, `opt`, `opt-proven-only`, or one of those with `-trap` and/or `-abort`. Each configuration has its
own target directory because cargo does not see the Lean-side settings. For the same reason,
`cargo fv` keeps a stamp per profile (`target/fv/<mode>/fv-stamp.<profile>`) of the Lean tools
(`lean-backend`, `clif-data-export`, `lean-regalloc`, `normalize.py`, `fv-rustc`, the codegen backend `.so`), `FV_SKIP`,
`FV_ONLY` and `package.metadata.fv`. When the stamp changes, it runs `cargo clean -p` on the
workspace members, so they are compiled again with the new tools or settings. Dependencies
are not cleaned.

### Report format

`target/fv-report.json` has one entry per compiled unit (a library, a binary, a test harness):
`package`, `crate_name`, `kind`, `src` (crate root), `counts`, and `functions`. Each function
has `symbol`, `instance` (the Rust item, from cg_clif's dump), `status` (`verified`,
`unverified` or `fallback`) and `reason`. Linked executables also have `binary`: how many
function symbols in the executable resolve to Lean-compiled code, plus any check failures.
The file covers the units of the last `cargo fv` command, fresh or rebuilt. The top-level
`mode`, `profile` and `theorem` say what "verified" refers to, and `panic` the panic strategy
and the codegen backend (also the second line of the summary).

## How it works

`cargo fv` runs cargo on the pinned nightly with `RUSTFLAGS=-Zcodegen-backend=<cg_clif>`
(see *Panics and unwinding*; `--panic-abort` adds `-Cpanic=abort -Zpanic-abort-tests`),
`--target aarch64-unknown-linux-musl`, `RUSTC_WRAPPER=fv-rustc`, `CARGO_INCREMENTAL=0`, the
linker `rust-lld` and the runner `qemu-aarch64-static`. First it runs a build (`cargo build`,
or `cargo test --no-run`) whose JSON artifact messages identify the units, then the report,
then `cargo run`/`cargo test` itself (everything is fresh by then).

`fv-rustc` passes every rustc invocation through unchanged, except codegen of a workspace
member for the target. Dependencies, the standard library (the prebuilt one, compiled by
LLVM), build scripts and proc macros are not changed. For a member it adds:

* `--emit=llvm-ir`: cg_clif then writes every function's CLIF to `<out-dir>/<unit>.clif/`
  (`<symbol>.unopt.clif`, the frontend's output, which is what we compile, plus `.vcode`).
  With a single codegen unit rustc afterwards tries to copy an `.ll` file that cg_clif never
  writes. `fv-rustc` recognises exactly that error, creates the empty file and runs rustc again.
* `-Csymbol-mangling-version=hashed`: v0 names of monomorphised iterator adapters are longer
  than the 255-byte file-name limit of those dump files.
* for executables and test harnesses, `-Clinker=fv-rustc`, so rustc runs `fv-rustc` in
  *linker mode* on the crate's objects before `rust-lld`.

Each codegen-unit object of a member (the `*.rcgu.o` members of a library's rlib after rustc,
or an executable's `*.rcgu.o` files at link time) then goes through this pipeline
(`rust/crates/cargo-fv/src/pipeline.rs`):

1. **Select**: the CGU's functions are the dumps whose symbol is a text symbol of the object
   (FuncIds `u0:N` are numbered per CGU, so a CGU is the unit of normalisation).
2. **Data and callees**: `clif-data-export` pairs every external-name use of the CLIF with
   cg_clif's relocations in the object. This gives the object symbol of every `symbol_value`
   (`--gvmap`: `.LdataN`, a named static, or with `--imported` a static of another crate)
   and of every callee declared only by FuncId
   (`--fnmap`: a function of another crate or CGU). The FuncId mapping is checked, never
   guessed: dense ref numbering, target kinds, the CGU's own functions map to their own
   symbols, one symbol per FuncId across all functions. Then `normalize.py --split --gvmap
   --fnmap --strip-srcloc` writes one CLIF file per function.
3. **Compile**: `lean-backend f.clif f.o` per function (`FV_JOBS` in parallel). One function
   per file means every call is a call of an extern. The theorem covers extern calls through
   its callee contract, and a function the backend rejects does not make its callers fall
   back: their calls reach cg_clif's code for it. Functions with a landing pad (`try_call`)
   are compiled too (*Panics and unwinding*).
4. **Safety net**: every symbol a Lean object references must be defined or referenced by
   cg_clif's object (or be a runtime helper: `mem*`, `__{u,}{div,mod}ti3`, all in every Rust
   executable); otherwise the function falls back. A calling-convention guard (`abi_guard`)
   would send functions whose signature or callees' signatures are passed differently by
   the two backends to the fallback. Its list is empty now: the one mismatch found (sret)
   was fixed in the backend, see *Limitations*.
5. **Merge** (`llvm-objcopy`, `rust-lld -r`):
   * local symbols of cg_clif's object that Lean code defines or references are renamed to a
     unique name (`__fv_<tag>_<name>`) and made global, so the references bind across objects;
   * cg_clif's definitions of the Lean-compiled functions are made **weak**;
   * the Lean objects are linked together (`ld -r`), get the same renaming, and one local
     marker `__fvlean$<symbol>` per function at the start of its code;
   * `rust-lld -r --unique cg_clif.o lean.o`: each strong Lean definition wins over the weak
     cg_clif one. Relocations are symbol-based, so every call and every vtable or
     function-pointer slot in cg_clif's code and data now reaches the Lean code. cg_clif's
     copy stays behind as unreferenced code in its own section, and `--gc-sections` removes it
     from executables;
   * the renamed symbols and markers are made local again. The object's interface to the rest
     of the program (its global symbols) is unchanged, so rlibs, cargo's pipelining and the
     final link are unaffected;
   * check: each Lean-compiled symbol of the merged object has its marker's address. If not,
     the CGU is left as cg_clif wrote it and all its functions fall back.
   * unwind tables: each Lean object has its own `.eh_frame` (FDEs relocated against its
     `.text`), so the merged object has FDEs for the Lean code and cg_clif's FDEs for its own
     sections (which reference cg_clif's section symbols, never the Lean code). The linker
     drops the FDEs of the sections `--gc-sections` removes, and builds `.eh_frame_hdr`.

**Data identity.** Lean code uses cg_clif's own data symbols (the renamed `.LdataN` and named
statics) and never copies data. Every static, vtable, panic `Location` and string constant
therefore has exactly one address, shared by cg_clif's code, the Lean code and other crates.
`static` and `static mut` identity, vtable comparisons (`ptr::eq` on `dyn` pointers) and
interior mutability all behave as under plain cg_clif. The alternative, `clif-data-export`'s
`; data:` copies, would give statics a second address and was rejected for that reason.

**Runtime.** In a cargo build, `memcpy`/`memset`/`memmove`/`memcmp` come from musl, the
128-bit division helpers from compiler-builtins, and the panic entry points from core/std. The
freestanding `scripts/rust-clif/rust-runtime.c` of the corpus tests is not linked.

### Panics and unwinding

The default is Rust's: `panic=unwind`. A panic unwinds with the DWARF unwinder of std's
`panic_unwind` (libunwind), which needs call frame information for every frame it passes
and, for frames that must run code during unwinding, a landing pad and an LSDA.

* **Lean frames** carry `.eh_frame` rows (`FV/Backend/Unwind.lean`, unverified and outside
  every theorem; the code never reads them). They mirror Cranelift's aarch64 unwind info for
  the backend's own frame: CIE as Cranelift's (`zR`, code alignment 4, data alignment -8,
  return address x30, CFA = sp+0, FDE pointers pc-relative `sdata4`); after
  `stp x29, x30, [sp, #-16]!` CFA = sp+16 with x29 at CFA-16 and x30 at CFA-8, after
  `mov x29, sp` CFA = x29+16, and after each callee-save store `str xN/qN, [sp, #o]` (block 0,
  before any call) the register at CFA + o - 16 - frameSize. `pc_begin` is an
  `R_AARCH64_PREL32` against `.text`. No epilogue rows, as in Cranelift: unwinding starts only
  at call sites. The `.text` bytes are unchanged (`scripts/lean-backend-encode-check.sh`).
* **Landing pads.** The shipped `rustc-codegen-cranelift-preview` of this nightly is built
  *without* cg_clif's `unwinding` feature: it drops cleanup blocks and compiles the
  `catch_unwind` intrinsic as a plain call. Plain `cargo test -Zcodegen-backend=cranelift`
  therefore runs no `Drop` during unwinding and a `catch_unwind` in cg_clif-compiled code
  does not catch (the panic reaches the test harness, which is LLVM code in the prebuilt
  libtest, so `#[should_panic]` works). `scripts/build-cg-clif-unwind.sh` builds cg_clif with
  the feature (the nightly's own cg_clif sources, commit from `rustc -vV`, against the
  `rustc-dev` component): it emits `try_call` with landing pads and LSDAs
  (`.gcc_except_table`), and `catch_unwind`/`Drop` behave as with LLVM. `cargo fv` uses it
  when it exists (`FV_CG_CLIF` overrides).
* **Landing pads are Lean code** (agent/fv-trycall): functions with `try_call`/
  `try_call_indirect` are compiled: the call is a block terminator, the handler successors are
  the landing pads (payload in x0), and the object gets cg_clif's LSDA in `.gcc_except_table`
  and a `zLPR` CIE with `rust_eh_personality` (`lean-backend --personality`). Callees with the
  `tail`/`preserve_all` convention and exception-table `context` items are rejected
  (fallback); cg_clif emits neither.
* **`try_call` is verified for normal returns** (agent/trycall-proof): a function whose
  `try_call`s call externs is inside `E2E.backend_correct_final` for the path where every
  callee returns normally (the call, its results, the jump to the normal-return successor).
  The report labels it **`verified (normal returns; unwinding trusted)`** and counts it among
  the verified functions, with a footnote giving how many there are. Nothing is claimed about
  unwinding: the landing pads, the payload on the handler edges, the LSDA and the `.eh_frame`
  rows are trusted. `try_call_indirect` is verified the same way (agent/indirect-proof). Every
  `try_call` function stays unverified under `--opt-proven-only` and after `i128`
  legalisation (those theorems cover `try_call`-free functions only).
* **Indirect calls are verified** (agent/indirect-proof): functions with `call_indirect`,
  `func_addr` (vtables, `fn` pointers, `dyn` dispatch) and `try_call_indirect` are inside
  `E2E.backend_correct_final` when the indirect calls have at most 8 register parameters and
  plain/`sret` signatures (otherwise "indirect call with stack-passed arguments or a
  special-purpose parameter"). An indirect call is covered when it reaches an extern (a
  function not compiled in the same file, e.g. a `dyn` method from another codegen unit or
  the standard library) under the contract `XCallsIndOk`; one that reaches a function of the
  same file is excluded by the run premise `TrapsExplicit.indirect`, as direct calls of
  functions of the file are. Under `--opt-proven-only` and after `i128` legalisation,
  `call_indirect` functions stay unverified (the mid-end simulation does not model them).
* With the shipped cg_clif (no unwinding build, or `FV_CG_CLIF=cranelift`), no function has a
  landing pad, `cargo fv` prints a note, and the program behaves as under plain cg_clif: the
  reference for comparisons is then plain cg_clif, not LLVM (`BASELINE=cg_clif
  examples/compare.sh`).
* `--panic-abort` restores the previous behaviour (`-Cpanic=abort -Zpanic-abort-tests`, each
  test in a child process). It always uses the shipped cg_clif: under panic=abort the unwinding
  build turns every call that may unwind into a `try_call` with a terminate edge (rustc's
  `abort_unwinding_calls`), which would fall back.

## Checking that the Lean code runs

* **Binary check** (automatic): after linking an executable, `fv-rustc` looks up every
  `__fvlean$<symbol>` marker in the executable's symbol table and checks that `<symbol>` has
  the same address, i.e. that the linked program calls the Lean code. The count is the
  "Lean in exe" column. A mismatch makes `cargo fv` exit 1 (it would be a bug in cargo fv).
* `--trap-replaced` overwrites cg_clif's (dead) code of every Lean-compiled function with
  `udf` traps in the objects, so executing it would crash. The tests pass with it, and
  `--gc-sections` drops those bodies from the executables anyway.
* `--no-fallback`: every function of the workspace members must be Lean-compiled.
* `examples/compare.sh DIR`: `cargo test` with LLVM (under qemu) against `cargo fv test`,
  test by test. `BASELINE=cg_clif` compares against plain cg_clif instead (the same backend
  and panic strategy `cargo fv` uses; the right reference with the shipped cg_clif, which has
  no landing pads).

## What is verified, and what is not

* **verified** = the function's machine code (Lean backend, register allocation checked by
  the Lean checker, Lean encoder) refines its CLIF under `E2E.backend_correct_final`
  (hypotheses: `docs/contracts/e2e.md`). Calls to other functions are extern calls in that
  theorem: the proof assumes the callee behaves as its CLIF (the callee contract), whether the
  callee is Lean-compiled, cg_clif-compiled or in std.
* **verified (normal returns; unwinding trusted)** = verified as above for a function with
  `try_call`s: the theorem covers the runs in which every callee of a `try_call` returns
  normally (with the callee contract `CalleeTryOk` for the exception payload registers); the
  unwinding path (landing pads, LSDA, unwind tables) is trusted.
* **Validation budget.** "verified" needs the lowering validator (`lowerCheck`, whose
  acceptance the theorem assumes) to accept the function. Its cost is near-linear in practice
  but grows, in the worst case, with the number of instructions times the number of values
  (it records the lowering's state after every statement, and its dataflow keeps a
  blocks × values table): the largest functions of `examples/` (about 2000 instructions and
  1500 values) take about 0.2 s. As a guard against pathological inputs, `lean-backend` does
  not run it on a function with more than 25000000 instructions × values
  (`Backend.validationBudget`; at the budget the validator takes about 1.5 s and under 1 GB,
  the largest function of `examples/` costs 3276540): such a function is compiled and
  reported **compiled, unverified** with the reason `validation budget: N instructions × values
  > 25000000, lowerCheck not run` (`lean-backend` prints `compiled, unverified (validation
  budget): …`). No function of `examples/` reaches it.
* Not verified: rustc and cg_clif (Rust → CLIF), `normalize.py`, `clif-data-export`, the
  object surgery above, the linker, std and dependencies (cg_clif or LLVM code), and
  everything the report lists as unverified or fallback. `--opt` runs unproven rules.
* The report is per function and per build; it does not cover the executable as a whole.

## Examples and results

* `examples/fv-demo`: a library with 19 unit tests: integer arithmetic, slices, enums,
  Option/Result, iterators, u128/i128, `dyn` traits and closures, four `should_panic` tests,
  `sret_interop`, six unwinding tests and `thread_locals` (`thread_local!` with a const and a
  lazy initializer, one instance per thread, checked across a spawned thread). `sret_interop` calls between Lean and cg_clif code
  through the struct-return convention, in both directions; the cg_clif side is kept by
  `package.metadata.fv.skip`. The unwinding tests (module `unwind`) panic through Lean frames
  without landing pads: `catch_unwind` with the payload checked, `Drop` during unwinding with
  an observable log (two guards in a cg_clif frame with a landing pad, dropped in order), a
  nested catch + `resume_unwind` through further Lean frames, a `should_panic` through
  Lean → cg_clif → Lean, and callee-saved registers (x19–x28 saved by the Lean frames between
  the panic and the catch) that must hold their values after the catch. There is also a
  binary: `cargo fv run -- 97 84 36`.
* `examples/survey`: the nine crates of the Rust CLIF survey (`scripts/rust-clif/corpus/*.rs`,
  used in place) as a workspace. Each crate's `tests/values.rs` checks the values in
  `tests/expected.txt`, which `gen-expected.sh` computes with rustc's LLVM backend for the
  same target (under qemu). There are 53 tests, including 9 `should_panic` ones.

Results (2026-09-30, agent/trycall-proof: `try_call` verified for normal returns, near-linear
lowering validator; `examples/compare.sh`, which requires every test outcome to match the
`cargo test` LLVM run; panic=unwind with the unwinding cg_clif, the default):

| | profile | tests | functions | verified | unverified | fallback | of which landing pad | Lean in exe |
|---|---|---|---|---|---|---|---|---|
| fv-demo | debug | 19/19 | 1346 | 1272 | 68 | 6 (skip) | 0 | 890 |
| fv-demo | release | 19/19 | 953 | 882 | 65 | 6 (skip) | 0 | 662 |
| survey | debug | 53/53 | 3179 | 3029 | 150 | 0 | 0 | 3179 |
| survey | release | 50/50 + 3 ignored (overflow checks off) | 2208 | 2091 | 117 | 0 | 0 | 2208 |
| vendor | debug | 187/187 + 2 ignored | 4399 | 4191 | 208 | 0 | 0 | 4273 |
| vendor | release | 187/187 + 2 ignored | 3082 | 2847 | 235 | 0 | 0 | 2872 |

After agent/indirect-proof (2026-10-01: `call_indirect`, `func_addr`, `try_call_indirect`
verified; debug, `examples/compare.sh` SAME for all three: fv-demo 19, survey 53, vendor 189
test outcomes): fv-demo 1320 verified of 1346 (20 unverified, 6 fallback), survey 3147 of 3179
(32 unverified), vendor 4302 of 4399 (97 unverified); of them `verified (normal returns;
unwinding trusted)`: 252, 493, 837. No function is unverified for an indirect call any more
(the remaining reasons: atomics/`bmask`/`fence`, `tls_value`, stack-passed parameters or call
arguments, calls of functions of the same file, rejected `i128` legalisations). Release
builds were not re-measured.

After agent/atomics-proof stage A (2026-10-01: `bmask`, `atomic_load`, `atomic_store` and
`fence` verified; `atomic_rmw`/`atomic_cas` not yet; debug, `examples/compare.sh` SAME for all
three): fv-demo 1323 verified of 1346, survey 3156 of 3179, vendor 4324 of 4399.

Of the verified, `verified (normal returns; unwinding trusted)`: fv-demo 231 / 204, survey
492 / 419, vendor 820 / 727 (debug / release). Before (main fbbd5d9, `try_call` functions
compiled but unverified) survey debug had 2537 verified of 3179. No function is over the
validation budget. `cargo fv test` wall time (a full rebuild of the workspace members, then
the tests under qemu): fv-demo 4 s / 3 s, survey 9 s / 7 s, vendor 16–20 s / 12–14 s (two
runs); plain cg_clif
`cargo test` in a fresh target directory: 0.3 s / 0.3 s, 0.9 s / 1.1 s, 3.6 s / 2.5 s. (Before
the near-linear validator, `lean-backend` ran for over an hour on each of the survey's largest
`try_call` test functions, and the survey build did not finish.)

With the shipped cg_clif (`FV_CG_CLIF=cranelift`, no landing pads) or `--panic-abort`
there are no landing-pad fallbacks:

| | configuration | tests | functions | verified | unverified | fallback | Lean in exe |
|---|---|---|---|---|---|---|---|
| fv-demo | debug, shipped cg_clif, unwind | 14/18, the same 4 fail under plain cg_clif | 1111 | 804 | 298 | 9 | 733 |
| fv-demo | release, shipped cg_clif, unwind | 14/18, likewise | 746 | 509 | 204 | 33 | 503 |
| fv-demo | debug, `--panic-abort` | 14/18, likewise (the 4 need unwinding) | 1104 | 799 | 296 | 9 | 731 |
| survey | debug, shipped cg_clif, unwind | 53/53 (= LLVM) | 3179 | 2224 | 928 | 27 | 3152 |

The tables count each unit separately: a library compiled as an rlib and as its unit-test
harness appears twice. Since landing pads are Lean code (agent/fv-trycall) there are no
landing-pad fallbacks; before, they were the price of panic=unwind with landing pads
(functions with a `Drop` value live across a call, closures run by `catch_unwind`, …), and
`--panic-abort` avoided them. In the survey, with `--panic-abort` or the shipped cg_clif,
every function of the nine survey libraries runs Lean code (`cargo fv build --workspace --lib
--no-fallback --panic-abort` passes). Unverified: landing pads, indirect calls and
atomics (`sret` functions are verified since agent/sret-proof: survey debug, panic=unwind,
`cargo fv test --no-run`: 1965 → 2537 verified of 3179, the 652 "sret parameter" functions
now verified or, 80 of them, reported for their indirect calls; 53/53 tests pass). Before panic=unwind (panic=abort,
13 fv-demo tests), `--opt-proven-only` (survey 53/53), `--opt` (fv-demo 13/13) and
`--trap-replaced` (fv-demo 13/13) gave the same test outcomes.

A crate with crates.io dependencies (`itoa`, `smallvec`, `crc32fast`; the dependencies are
compiled by cg_clif) also passed (unit tests and a doctest, same outcomes as `cargo test`;
checked with panic=abort).

### Atomics, `bmask`, `fence`, and the vendored real-world crates (agent/fv-fallback)

`atomic_load`/`atomic_store`/`atomic_rmw`/`atomic_cas`/`fence` and `bmask` compile since
agent/fv-fallback: the Cranelift non-LSE lowering (cg_clif's aarch64 flags have `has_lse=0`),
i.e. `ldar`/`stlr` and the `atomic_rmw_loop`/`atomic_cas_loop` LL/SC pseudo-instructions
(`ldaxr`/`stlxr` loops over the fixed registers x24–x28), `csetm` for `bmask`, `dmb ish` for
`fence` — all encode-checked byte-for-byte against llvm-mc and differentially executed
against Cranelift-native on the atomic/bmask/fence runtests. `bmask`, `atomic_load`,
`atomic_store` and `fence` are in E and inside `E2E.backend_correct_final` (single-threaded
Arm model, `docs/decisions/arm-model.md`, "Atomics"). `atomic_rmw`/`atomic_cas` are still
outside E (reported as "outside clif-subset-v2 E"). The stack-slot allocator rejects the loop
pseudo-instructions (regalloc2, the default, handles their fixed registers).

`examples/vendor` vendors dep-free crates.io crates (`crc32fast`, `itoa`, `memchr`, `hex`,
`bitflags`, `cfg-if`, `once_cell`) plus a `harness` crate with reference-value tests, to
measure and drive out fallbacks on real code. Vendor patches: dev-dependencies pruned,
`quickcheck!` blocks replaced by deterministic LCG `#[test]`s, itoa's optional `no-panic`
dependency removed, the aarch64-specialized crc32fast tests dropped (their
`stable_arm_crc32_intrinsics` cfg is not set by cg_clif, which made the test set differ
between `cargo test` and `cargo fv test`). The `once_cell` `race` module is what exercises
the atomics. Release-mode functions whose unoptimised CLIF references a data object that
Cranelift's optimiser removed from cg_clif's object (a dead panic path's `Location`, …) are
retried with the `.opt.clif` dump (`docs/research/rust-route.md`, "agent/fv-fallback"), which
matches the code cg_clif actually emitted.

Results (`cargo fv build` then `cargo fv report`; "unwind" = the default panic=unwind with the
landing-pad cg_clif, whose landing-pad fallbacks are the unwinding design, see above;
"abort" = `--panic-abort`, the configuration of the "before" measurements):

| workspace | profile | panic | functions | verified | unverified | fallback | of which landing pad | of which skip |
|---|---|---|---|---|---|---|---|---|
| fv-demo | debug | unwind | 478 | 300 | 97 | 81 | 78 | 3 (`metadata.fv.skip`) |
| fv-demo | release | unwind | 325 | 185 | 63 | 77 | 74 | 3 |
| survey | debug | unwind | 460 | 350 | 55 | 55 | 55 | — |
| survey | release | unwind | 245 | 159 | 39 | 47 | 47 | — |
| vendor | debug | unwind | 625 | 458 | 126 | 41 | 41 | — |
| vendor | release | unwind | 256 | 147 | 78 | 31 | 31 | — |
| fv-demo | debug | abort | 479 | 351 | 125 | 3 | — | 3 |
| fv-demo | release | abort | 320 | 227 | 90 | 3 | — | 3 |
| survey | debug | abort | 454 | 394 | 60 | 0 | — | — |
| survey | release | abort | 239 | 195 | 44 | 0 | — | — |
| vendor | debug | abort | 625 | 491 | 134 | 0 | — | — |
| vendor | release | abort | 250 | 162 | 88 | 0 | — | — |

Before agent/fv-fallback (the same builds, panic=abort): fv-demo debug 2 fallbacks (skip),
fv-demo release 7 (5 missing `allocNNN`, 2 skip), survey release 13 (all missing `allocNNN`),
vendor debug 10 (9× atomics/bmask/fence unsupported), vendor release 16 (8 missing
`allocNNN`, 8 atomics/bmask/fence). The missing-`allocNNN` fallbacks are gone (`.opt.clif`
retry), and every atomic/bmask/fence function compiles (flagged unverified: vendor 9 debug,
7–8 release). The only fallbacks left are `metadata.fv.skip` and, under panic=unwind,
landing pads. `examples/compare.sh examples/{fv-demo,survey,vendor}` (debug and `--release`)
report the same test outcomes as `cargo test` (fv-demo 18/18, survey 53/53, vendor 189/189).

### Thread-local storage and dead blocks (agent/fv-lcheck-tls)

* **`tls_value`** (the `thread_local!` accessors: `symbol tls` global values) compiles, flagged
  unverified ("tls_value (outside backend_correct)"). The lowering is Cranelift's for cg_clif's
  `tls_model=elf_gd`: `ElfTlsGetAddr`, the TLSDESC sequence `adrp x0, :tlsdesc:v` /
  `ldr xT, [x0, :tlsdesc_lo12:v]` / `add x0, x0, :tlsdesc_lo12:v` / `blr xT` (relocations
  `R_AARCH64_TLSDESC_ADR_PAGE21`/`LD64_LO12`/`ADD_LO12`/`CALL`, the variable an `STT_TLS`
  symbol), then `mrs xT, tpidr_el0` and `add x0, x0, xT`; x0 is a fixed def and xT an early
  def (the resolver preserves every other register). The code and relocations are identical
  to cg_clif's and to `llvm-mc`'s (`lean-backend-encode-check.sh`, `corpus/clif-regress/tls_elf_gd.clif`
  and random forms), and `rust-lld` relaxes the sequence in the static executable
  (`movz`/`movk`/`nop`/`nop`). `clif-data-export` names the variable of each `tls_value`
  from the function's TLSDESC relocations (paired with the `.vcode`'s `elf_tls_get_addr`
  lines, in code order).
* **Dead blocks.** The lowering validator (`lowerCheck`) rejected functions with blocks that
  have no path from the entry (cg_clif's dead cleanup blocks, e.g. the test instances of
  `once_cell::imp::…::initialize::{closure#0}`): its availability dataflow gave such a block
  every value of the function at its entry, including values computed from the block's own
  results, which fails the certificate's closure condition. The dataflow now keeps a value at
  a block entry only if its definition's operands are available there too. The lowering was
  correct; the certificate and its soundness proof (`lowering_of_check`, generic in the
  entry-value lists) are unchanged. Regression file: `corpus/clif-regress/dead_cleanup.clif`
  (in `lean-e2e-check`'s default corpus).

`cargo fv test --no-run` then `cargo fv report` (panic=unwind), before → after:

| workspace | profile | functions | verified | fallback before | fallback after | tls_value (unverified) |
|---|---|---|---|---|---|---|
| fv-demo | debug | 1346 | 823 | 6 (skip) | 6 (skip) | 4 |
| fv-demo | release | 953 | 544 | 6 (skip) | 6 (skip) | 4 |
| survey | debug | 3179 | 1932 | 0 | 0 | 0 |
| survey | release | 2208 | 1361 | 0 | 0 | 0 |
| vendor | debug | 4399 | 2545 (2533 before) | 15 (12 lowerCheck, 3 TLS) | 0 | 3 |
| vendor | release | 3082 | 1569 | 3 (TLS) | 0 | 3 |

(fv-demo's counts include the new `tls` module.) `examples/compare.sh` reports SAME for
fv-demo 19/19, survey 53/53 and vendor 189/189, debug and `--release`.

## Limitations

* Target `aarch64-unknown-linux-musl` only. The host is x86_64, so executables run under
  qemu. Linking always uses `rust-lld`.
* Only workspace members are compiled by the Lean backend. Dependencies use cg_clif and std
  is the prebuilt LLVM one; which crates get the Lean backend may become configurable later.
* panic=unwind: full unwinding semantics (`Drop` during unwinding, `catch_unwind` in the crate)
  need the unwinding cg_clif (Install, 5); the shipped one has no landing pads at all. The
  landing pads of Lean-compiled functions and their LSDA are compiled but not verified: the
  theorem covers `try_call`s up to the normal return only.
* Library crate types `lib`/`rlib`, binaries and test harnesses. `dylib`, `cdylib`,
  `staticlib` and proc macros build with plain cg_clif.
* `RUSTFLAGS` from the environment are kept (with ours appended). `build.rustflags` from
  `.cargo/config.toml` is overridden, as with any `RUSTFLAGS`.
* Debug info describes cg_clif's code, not the Lean code.
* Doctests are compiled by rustdoc with LLVM (with `-Cpanic=abort` under `--panic-abort`) and
  linked against the member crate's Lean-compiled rlib.
* The calling conventions of the two backends must agree. cargo fv found one mismatch:
  lean-backend passed the arguments after an sret pointer from x1 instead of x0. That is
  fixed in the backend (f52e514), and fv-demo's `sret_interop` is the regression test.
  i128 register pairs, more than 8 (stack-passed) arguments and `uext`/`sext` narrow
  arguments were spot-checked against Cranelift and agree.
* In release builds, a function whose unoptimised CLIF references data that Cranelift's
  optimiser removed falls back. We compile the unoptimised CLIF, and the object has no symbol
  for that data.

## Troubleshooting

* `no such command: fv`: put `rust/target/release` on `PATH`.
* `… missing (FV_ROOT=…)`: build the named tool (see Install).
* `toolchain … not found`: install the nightly with the component and target (Install, 1).
* `--panic-abort`: a `should_panic` test fails with an exec error: register qemu with
  binfmt_misc (Install, 2).
* `catch_unwind` does not catch or `Drop` does not run during unwinding: the build uses the
  shipped cg_clif (the summary's `panic=` line says which); build the unwinding one (Install, 5).
* A function falls back and you want to know why: `cargo fv report --functions`, or
  `target/fv-report.json`. `--keep-temps` keeps the normalised CLIF (`split/`), the
  per-function objects (`o/`) and the merge inputs in `target/fv/<mode>/tmp/<tag>/`.
* A test fails under `cargo fv test` but passes under `cargo test`: bisect with
  `FV_SKIP=<path substring>` / `FV_ONLY=…`; changing them rebuilds the members. Then look at
  the function's CLIF and `llvm-objdump -d` of its object in `--keep-temps`. That is how the
  sret mismatch was found.

# `cargo fv`: building Rust crates with the Lean backend

`cargo fv build|run|test` works like the corresponding cargo command, but the functions of
your crate **and of its dependencies** are compiled by the all-Lean CLIF → AArch64 backend of
this repository. The Rust frontend is rustc_codegen_cranelift (cg_clif): it lowers Rust to
CLIF, and for every function of every crate compiled for the target (the workspace members
and all their dependencies: registry, git and path packages) the Lean backend compiles that
CLIF again. Only std (the prebuilt standard library) and the host-side code that is not part
of the program (build scripts, proc macros) are not. The Lean code replaces cg_clif's code
for that function. Functions the Lean backend cannot compile keep cg_clif's code
(**fallback**), so the build never fails because of the Lean backend. After each build,
`target/fv-report.json` and a summary on stderr list every function as one of:

* **verified**: compiled by the Lean backend and inside the end-to-end theorem
  (`E2E.backend_correct_final`, or `E2E.backend_correct_opt_proven` with `--opt-proven-only`;
  for `i128` functions `E2E.backend_correct_legal`, without `--opt`);
* **compiled, unverified**: compiled by the Lean backend but outside the theorem (the reason
  is given, e.g. an indirect call, or an `i128` function under `--opt`), or over the
  validation budget (see *What is verified, and what is not*);
* **fallback**: cg_clif's code (the reason is given).

```
$ cd examples/deps && cargo fv test
   Compiling deps-demo v0.1.0 (…/examples/deps)
cargo fv report — aarch64-unknown-linux-musl debug profile, mode plain
  verified = compiled by the Lean backend and inside E2E.backend_correct_final
  package                kind  crate root             functions  verified unverified  fallback   Lean in exe
  deps-demo              test  tests/crates.rs             2358      2338          0        20         19808
  …
  regex-automata         dep   src/lib.rs                  5039      5039          0         0
  serde_json             dep   src/lib.rs                  1177      1127          0        50
  …
  your crate(s)                                            4056      4028          0        28
  dependencies                                            16965     16793          3       169
  total                                                   21021     20821          3       197
  std (not compiled by us: prebuilt std/core/alloc rlibs, plus compiler_builtins and musl libc)
  exe deps-demo (test tests/crates.rs): 21682 functions: Lean 19808 (your crate(s) 3052, dependencies 16756), cg_clif fallback 142, std (prebuilt) 1732, other not compiled by us 0
  …
cargo fv: 20824 of 21021 functions compiled by the Lean backend (20821 verified): your crate(s) 4028 of 4056 (4028 verified), dependencies 16796 of 16965 (16793 verified); report: …/target/fv-report.json
     Running unittests src/lib.rs (…)
test tests::perms ... ok
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
cargo fv link-proof [--exe SUBSTR]… [--crate NAME] [--out DIR] [--prune] [--lean FILE --module NAME] [--entries a,b]
```

Options of `cargo fv` (all other options go to cargo unchanged):

| option | effect |
|---|---|
| `--opt` | run the Lean mid-end with every rule. Most simplify rules are unproven, so no function is reported verified. |
| `--opt-proven-only` | run the Lean mid-end with the proven rule set; verified = inside `E2E.backend_correct_opt_proven` |
| `--no-fallback` | fail (exit 1, before running anything) unless every function of every workspace member runs Lean code (dependencies may keep fallbacks, e.g. float code; the report lists them) |
| `--trap-replaced` | overwrite cg_clif's code of every Lean-compiled function (members and dependencies) with `udf` traps (see *Checking that the Lean code runs*) |
| `--members-only` | only the workspace members go through the Lean backend; dependencies are plain cg_clif (the behaviour before agent/fv-deps; own target directory) |
| `--keep-temps` | keep the per-codegen-unit work directories (`target/fv/<mode>/tmp/`), with what `cargo fv link-proof` needs: per function the CLIF file `lean-backend` compiled, `lean-regalloc`'s output for it and the linked symbol names (`fv-link.json`), per executable the link map |
| `--panic-abort` | build with `-Cpanic=abort -Zpanic-abort-tests` (the pre-unwinding behaviour; the shipped cg_clif; own target directory; the configuration of the binary-level theorem: no unwinding through Lean frames) |
| `--no-binary-check` | skip the per-executable binary check (see *The executable as a whole*); without it the build keeps what the check reads (the per-function CLIF and `lean-regalloc` output, `fv-link.json`, the link maps; not the objects) in `target/fv/<mode>/tmp/` |
| `--lean-link` | the Lean linker writes the Lean-compiled code of every executable (L2b, docs/research/lean-linker.md): the codegen units keep cg_clif's object (our functions weak), each executable gets the Lean code as one region (`.text.fvlean`, rust-lld links the rest around it) whose bytes `lake exe lean-link` computes with the executable compiler `Link.compileExe` (the input conditions `InScopeP`, then `Link.leanLink`: placement, relocation, checks) and writes into the executable; such an executable is covered by `Link.compileExe_correct` with no per-crate proof (L1; `lean-link` prints `written by Link.compileExe`). On a program outside `InScopeP` it prints the failing conditions and links with `Link.leanLink` alone (`written by Link.leanLink`): the crate's linker facts and the code part of the binary facts are then still theorems (`Link.leanLink_linkerOk`, `Link.leanLink_code`). The facts about rust-lld's output (headers, cg_clif's data objects, the symbol table, the region's segment) are `leanLink`'s checks (`Link.binOk_leanLink`). Unverified functions, and self-calling functions that take their own address, keep cg_clif's code. Needs `lake build lean-link`; implies `--keep-temps`; own target directory |

`cargo fv report` prints the summary of the last build again. `--functions` lists every
function with its status and reason, and `--json` prints `target/fv-report.json`.

Environment variables:

| variable | effect |
|---|---|
| `FV_JOBS` | `lean-backend` processes at a time in the whole build, across all crates cargo compiles in parallel (default: number of CPUs; file-lock slots in `target/fv/<mode>/tmp/slots/`) |
| `FV_SKIP_DEPS=a,b` | dependency packages (Cargo package names) that keep plain cg_clif |
| `FV_SKIP=pat,…` / `FV_ONLY=pat,…` | debugging: functions whose symbol or Rust path contains a pattern fall back / only those are compiled |
| `FV_TOOLCHAIN` | the nightly (default `nightly-2026-09-26`) |
| `FV_CG_CLIF` | the codegen backend: a cg_clif `.so`, or `cranelift` for the shipped one (default: `target/cg_clif-unwind/librustc_codegen_cranelift.so` of the checkout if it exists and panic=unwind, else `cranelift`) |
| `FV_ROOT` | the repository checkout with the tools |
| `FV_OBJCOPY`, `FV_AR`, `FV_RUST_LLD`, `FV_PYTHON` | tool paths |
| `CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER` | the runner (default `qemu-aarch64-static`) |

Per package, `Cargo.toml` can keep functions on cg_clif, and the workspace's packages can keep
whole dependencies on cg_clif:

```toml
[package.metadata.fv]
skip = ["interop::cg_clif_"]   # substrings of the symbol or the Rust path
skip-deps = ["ring"]           # dependency packages compiled by plain cg_clif
```

(`skip-deps` is read from every workspace member and from `[workspace.metadata.fv]`;
`FV_SKIP_DEPS` adds to it.)

Artifacts are in `target/fv/<mode>/aarch64-unknown-linux-musl/<profile>/…`, where `<mode>` is
`plain`, `opt`, `opt-proven-only`, or one of those with `-members` (`--members-only`), `-trap`
and/or `-abort`. Each configuration has its own target directory because cargo does not see
the Lean-side settings. For the same reason, `cargo fv` keeps a stamp per profile
(`target/fv/<mode>/fv-stamp.<profile>`) of the Lean tools (`lean-backend`, `clif-data-export`,
`lean-regalloc`, `normalize.py`, `fv-rustc`, the codegen backend `.so`), `FV_SKIP`, `FV_ONLY`,
`package.metadata.fv` (`skip`, `skip-deps`) and `FV_SKIP_DEPS`. When the stamp changes, it
deletes the profile's whole target-side output (`target/fv/<mode>/aarch64-unknown-linux-musl/<profile>/`,
members and dependencies, including their build-script runs) and the unit reports, so every
crate is compiled again with the new tools or settings. Host-side artifacts (build scripts,
proc macros, `target/fv/<mode>/<profile>/`) do not depend on the Lean side and stay.

### Report format

`target/fv-report.json` has one entry per compiled unit (a library, a binary, a test harness):
`package`, `crate_name`, `kind`, `src` (crate root), `dep` (true for a dependency: not a
workspace member), `counts`, and `functions`. Each function
has `symbol`, `instance` (the Rust item, from cg_clif's dump), `status` (`verified`,
`unverified` or `fallback`) and `reason`. The top level has `totals` and its split into
`members` ("your crate(s)") and `deps` ("dependencies"); std is not compiled by us and has no
function counts. Linked executables also have `binary`: how many function symbols in the
executable resolve to Lean-compiled code (members and dependencies), plus any check failures,
and `origin`: the executable's functions (distinct addresses) attributed through the link map
to Lean code of the members (`lean_members`) or of the dependencies (`lean_deps`, and per
package `lean_by_package`), cg_clif code of a crate we compiled (`cg_clif`: fallbacks and
cg_clif-generated helpers without a CLIF dump), the prebuilt sysroot (`prebuilt`: std, core,
alloc, compiler_builtins, musl libc) and other inputs (`other`: crates outside the scope with
`--members-only`/skip-deps). In the summary, dependency libraries are the rows of kind `dep`,
followed by the `your crate(s)` / `dependencies` / `total` rows, one `exe` line per
executable with that attribution (`Lean in exe per dependency`), and the unverified and
fallback reasons by count, separately for your crate(s) and the dependencies.
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

`fv-rustc` passes every rustc invocation through unchanged, except codegen of a crate for the
target: rustc's `--target` is `aarch64-unknown-linux-musl`, it emits `link`, and the crate
type is `lib`/`rlib`/`bin` or a test harness. That covers the workspace members and every
dependency (cargo passes dependencies `--cap-lints`, `-C metadata`, `-C extra-filename`,
`-C embed-bitcode=no`, `--crate-type lib`: the unit is named `<crate><extra-filename>` like
its rlib, and the hashed mangling makes its symbol names unique). Not changed: host crates
(build scripts `build_script_build`, proc macros like `serde_derive`, and their own
dependencies, which cargo compiles without `--target`, for x86_64), dependencies excluded by
`--members-only`/skip-deps, and the standard library (prebuilt, compiled by LLVM). For a
crate it compiles it adds:

* `--emit=llvm-ir`: cg_clif then writes every function's CLIF to `<out-dir>/<unit>.clif/`
  (`<symbol>.unopt.clif`, the frontend's output, which is what we compile, plus `.vcode`).
  With a single codegen unit rustc afterwards tries to copy an `.ll` file that cg_clif never
  writes. `fv-rustc` recognises exactly that error, creates the empty file and runs rustc again.
* `-Csymbol-mangling-version=hashed`: v0 names of monomorphised iterator adapters are longer
  than the 255-byte file-name limit of those dump files.
* for executables and test harnesses, `-Clinker=fv-rustc`, so rustc runs `fv-rustc` in
  *linker mode* on the crate's objects before `rust-lld`.

Each codegen-unit object of such a crate (the `*.rcgu.o` members of a library's rlib after rustc,
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
* **`try_call` is verified for normal returns** (agent/trycall-proof, agent/trycall-contract):
  a function whose `try_call`s call externs is inside `E2E.backend_correct_final` for the path
  where every callee returns normally (the call, its results, the jump to the normal-return
  successor). The report labels it **`verified (normal returns; unwinding trusted)`** and counts
  it among the verified functions, with a footnote giving how many there are. Nothing is
  claimed about unwinding: the landing pads, the payload on the handler edges, the LSDA and the
  `.eh_frame` rows are trusted. `try_call_indirect` is verified the same way
  (agent/indirect-proof). A `try_call`'s callee may take stack-passed arguments
  (agent/last-unverified). Every `try_call` function stays unverified under `--opt-proven-only`
  (that theorem covers `try_call`-free functions only); after `i128` legalisation `try_call` is
  covered (`E2E.backend_correct_legal`, agent/last-unverified), `try_call_indirect` is not.
  Between agent/callee-fix and agent/trycall-contract (2026-10-02) these functions were reported
  **compiled, unverified** (`try_call: callee contract CalleeTryOk not yet satisfiable (theorem
  vacuous)`): the callee contract `CalleeTryOk` fixed the exception payload registers x0/x1 to
  `X.call`'s world, which a callee that does not write them cannot meet. They are now dead on the
  normal return (havocked there; the register-allocation checker forgets them on that edge only)
  and `CalleeTryOk` constrains only the results (docs/contracts/e2e.md, "`try_call` payload
  registers"), with a witness (`E2E.backend_correct_final_try_witness`).
* **Indirect calls are verified** (agent/indirect-proof): functions with `call_indirect`,
  `func_addr` (vtables, `fn` pointers, `dyn` dispatch) and `try_call_indirect` are inside
  `E2E.backend_correct_final` when the indirect calls have at most 8 register parameters and
  plain/`sret` signatures (otherwise "indirect call with stack-passed arguments or a
  special-purpose parameter"). Calls are interpreted in a function-free activation program
  under `XCallsIndOk`/`XCallsOk`; the linking theorem supplies the contracts for compiled
  program callees, including the caller itself. Under `--opt-proven-only` `call_indirect`
  functions stay unverified (the mid-end simulation does not model them); after `i128`
  legalisation a `call_indirect` without `i128` operands is covered.
* **Recursion**: `cargo fv` compiles the original self-call directly, without an extern alias
  or a renamed copy of the function. Taking one's own function address is supported too.
  Recursive calls use the same per-activation callee contracts as other calls
  (`docs/contracts/e2e.md`, "Calls of the function itself"). This does not supply an
  unbounded stack: `compileExe_correct` still requires no reachable call cycle.
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
  the same address, i.e. that the linked program calls the Lean code. The markers of the
  dependencies' Lean-compiled functions are in their rlibs, so they count too. The count is
  the "Lean in exe" column; the `exe` lines split it per crate through the link map (`Lean in
  exe per dependency`). A mismatch makes `cargo fv` exit 1 (it would be a bug in cargo fv).
* `--trap-replaced` overwrites cg_clif's (dead) code of every Lean-compiled function, members
  and dependencies, with `udf` traps in the objects, so executing it would crash. The tests
  pass with it, and `--gc-sections` drops those bodies from the executables anyway.
* **Which Lean code ran**: `scripts/fv-exec-trace.py EXE [args]` runs an executable built with
  `--keep-temps` (whose link map stays in `target/fv/<mode>/tmp/link-<tag>.map`) under
  `qemu-aarch64-static -d exec,nochain` and counts, per crate, the Lean-compiled functions
  (marker at the address) and the other functions the run executed. For examples/deps see
  *Dependencies* below.
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
  normally (with the callee contract `CalleeTryOk` for its results); the unwinding path
  (landing pads, LSDA, unwind tables) is trusted.
* **Non-vacuity.** Every top-level theorem has a witness that its contract premises can all
  hold for realistic callees (docs/contracts/e2e.md, "Non-vacuity";
  `E2E.backend_correct_final_witness`, `E2E.backend_correct_final_id`, and for functions with
  `try_call`s `E2E.backend_correct_final_try_witness`).
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
  budget): …`). In `examples/` only the fully unrolled SHA-256/SHA-512 round functions of
  the `sha2` dependency (`sha2::sha{256,512}::soft::unroll::compress_block`, 52–604 M) reach
  it (examples/deps).
* Not verified (trusted): rustc and cg_clif (Rust → CLIF), `normalize.py`,
  `clif-data-export`, the object surgery above and the linker (both checked, for the
  program's code, data objects and symbols, by the binary check), std (the prebuilt standard
  library: std/core/alloc, compiler_builtins, musl libc; LLVM code), dependencies excluded by
  `--members-only`/skip-deps (cg_clif code), and everything the report lists as unverified
  or fallback (cg_clif code). `--opt` runs unproven rules. Build scripts and proc macros
  (e.g. `serde_derive`) run on the host at build time and are plain rustc: they are not part
  of the target program, but the code they generate is, and it is compiled like any other
  code of the crate that uses it. The executable's `exe` line counts the prebuilt functions.
* The report is per function and per build. For the executable as a whole see below:
  *The executable compiler* (`--lean-link`: the guarantee is the general theorem
  `Link.compileExe_correct`, no per-executable proof) and the binary check; *Proving a crate*
  gives an optional, independent Lean-checked certificate.

### The executable compiler (`--lean-link`, L1)

With `--lean-link`, the Lean-compiled code of every executable is written by the executable
compiler `Link.compileExe` (`lake exe lean-link`: the input conditions `InScopeP`, then the Lean
linker `Link.leanLink`). When `lean-link` prints `written by Link.compileExe`, the executable is
covered by `Link.compileExe_correct` (docs/contracts/e2e.md, "The executable compiler"), proven
once for every input: whenever code outside the program calls one of its Lean-compiled
functions from which no call cycle is reachable, per AAPCS64 and its contract, the
executable's own instructions refine the whole-program CLIF run. Nothing is generated or
checked per executable for that guarantee: the facts about the compiled code are theorems, and
the facts about the bytes rust-lld wrote (headers, cg_clif's data objects, the symbol table,
the region's segment) are checks inside `leanLink`, so a failure is a link error, not a weaker
guarantee. The remaining premises are the contracts of the code outside the program and that
the CLIF run traps only explicitly. When `lean-link` prints `written by Link.leanLink` (the
program fails an input condition, which it names), the executable is linked the same way but
not covered by `compileExe_correct`; the binary check and `link-proof` below still apply.

The binary check (below) and `cargo fv link-proof`/`crate-proofs/` (*Proving a crate*) stay
available as an **independent certificate**: they re-decide the checks on the linked file and
for the regalloc2 allocation as given, by compiled evaluation (`native_decide`). They are not
needed for the guarantee of `--lean-link` executables.

### The executable as a whole (binary check)

After the build, `cargo fv build`/`test`/`run` checks every linked executable with
Lean-compiled code against the binary-level theorem `E2E.Binary.binary_correct_of_checks`
(docs/contracts/e2e.md, "Binary level (M9)"): it runs `cargo fv link-proof` on the executable
(into `target/fv/<mode>/bin-check/<tag>/`) and `link-check --prune`, which decide the crate
checker (`LinkSys.Ok`), the binary checks (the executable's code is the compiled code with
resolved relocations — `cargo fv` links with lld's `--no-relax` so the address pairs stay as
emitted —, its data objects and symbols are the program's) and the stack bound, and prints one
verdict per executable:

```
cargo fv: binary …/values-5203fc787ef73bb4: verified: E2E.Binary.binary_correct holds for its 493 Lean-compiled functions; stack: 3008 bytes at most (no call cycle)
cargo fv: binary …/fv_demo: verified: E2E.Binary.binary_correct (binary_correct_depth for the functions whose calls reach a call cycle: their stack stays a premise) holds for its 551 Lean-compiled functions; stack: recursive: the calls of 26 function(s) reach a call cycle (their stack stays a premise); the other 525: 1744 bytes at most
cargo fv: binary check: 18 of 18 executable(s) verified (docs/contracts/e2e.md, "Binary level (M9)")
```

or `not verified: …` with the failing check (`binary check failed: FAIL code=… — BIN …`, or the
first function failing `LinkSys.Ok`, the others still covered). *Verified* means: whenever code
outside the program calls one of these functions per AAPCS64 and its contract (`OutsideCall`:
arguments, free stack of the printed size, its CLIF-visible memory related to the machine's), in
a machine state holding the executable's read-only bytes, the machine refines the
whole-program CLIF run; the premises left are the contracts of the code outside the program
(std, musl, fallback functions) and that CLIF traps only explicitly. The verdict is computed by
`link-check` (compiled Lean); for a kernel-checked certificate generate the proof with `cargo fv
link-proof --lean` (below). `--no-binary-check` skips it (its cost grows with the number of
Lean-compiled functions of each executable: under a second per survey executable).

## Proving a crate (`cargo fv link-proof`, optional)

Optional: an independent, standalone certificate per crate. For executables linked with
`--lean-link` by `Link.compileExe` the guarantee is the general theorem
`Link.compileExe_correct` (*The executable compiler* above); no per-crate proof is needed.

`E2E.backend_correct_program` covers a whole program: the linked code of a set of functions,
each calling the others' compiled code, refines the program's CLIF run; only calls outside the
set go to a base environment whose contracts stay premises (std, other crates, the runtime).
For a crate built by `cargo fv`, its premise `LinkSys.Ok` can be checked and proven per crate
(docs/contracts/e2e.md, "Crate-level instance"):

```
$ cd examples/survey && cargo fv test -p g_u128 --keep-temps
$ cargo fv link-proof --exe /g_u128/ --exe /values- --crate g_u128 --prune \
    --lean ../../crate-proofs/Crates/GU128.lean --module GU128
cargo fv link-proof: 19 functions of 1 codegen unit(s) of …/values-b9a5804fcd4b2231 (skipped 0), 68 addresses (0 names unresolved) → …/target/fv/link-proof
link-check: …/values-b9a5804fcd4b2231
  static checks (the validators): 0 function(s) fail
  static checks done in 95 ms
  19 functions, 68 link-map addresses, 30 CLIF image symbols, D = 144; checked in 100 ms
  --prune: 19 of 19 functions pass (0 dropped)
  okB: true
  relocations: 6 bl, address pairs 0 nop+adr, 0 adrp+add, 68 adrp+ldr (GOT), 0 TLSDESC sequences
  binary checks done in 22 ms
  binary: ok (19 functions, 865 words, 38 data objects, 68 symbols)
  wrote ../../crate-proofs/Crates/GU128.lean
  19 functions, 19 entries
$ cd ../../crate-proofs && lake build Crates.GU128
```

1. Build with `cargo fv build` or `test` (the inputs are kept unless `--no-binary-check`;
   `--keep-temps` keeps the whole work directories).
2. `cargo fv link-proof` picks the executable whose path contains every `--exe` (default: the
   only one linked) and the Lean-compiled, **verified** functions of its codegen units (`--crate NAME`:
   only the crate's own units, `NAME-<hash>`), and writes `--out` (default
   `target/fv/link-proof`): `fns/<i>.clif` (the CLIF with every name replaced by the symbol it
   is linked as), `fns/<i>.ra.json` (`lean-regalloc`'s output) and `link.json` (the functions,
   the data objects they reach, and the link-map addresses of them and of every name they
   use). It then runs `lake exe link-check` on it (build it once: `lake build link-check`),
   passing `--prune`, `--lean`, `--module`, `--entries`.
3. `lake exe link-check DIR` compiles every function again in Lean from its CLIF and allocation,
   evaluates the checker `E2E.LinkCheck.okB` and prints the failing premises of `LinkSys.Ok` per
   function, with details (the call site, the undeclared name), and a count per premise.
   `--prune` drops the failing functions and their callers (transitively), so the rest is
   closed under calls. Recursive calls retain their original names and enter the same
   function's code; no self-call alias is synthesized. Then the **binary checks**
   (`FV/E2E/BinCheck.lean`, e2e.md "Binary level (M9)") read the executable: every compiled word
   of the (pruned) program at its address, every relocation resolved (`bl` targets, address
   pairs as emitted with resolved immediates, GOT slots, TLSDESC in lld's local-exec form), the data objects the program reaches and
   the symbol table against the link map; `BIN …` lines say what differs, `binary: ok` /
   `binary: FAIL …` is the verdict. `--profile` times the slowest functions. Exit status 0
   iff the (pruned) set passes both.
4. With `--lean FILE --module NAME` (and the checks passing) it writes the proof: `okB_input`
   (`native_decide`: `globalB_input` for the program, `sliceK_ok` per slice of 32 functions),
   `link_ok` (`LinkSys.Ok` of the crate for every base environment satisfying `BaseOk`),
   `base_closed` (the base premises are satisfiable; written when no function has
   `tls_value`), `entries_present`, `correct_<i> : CrateStmt input "<symbol>"` for every
   function (`--entries a,b`: those), and `bin_ok (file) : Elf.Agrees file exAll → BinOk input
   dataObjs file` (the binary checks by `native_decide` on excerpts of the executable embedded
   in the files). Up to 32 functions it is one file; beyond, `FILE`
   imports `NAME/Input.lean` and one module per slice, `NAME/SliceK.lean` (rewritten on every
   run), which Lake builds in parallel. The proof does not trust `link-check`: `native_decide`
   evaluates `okB` and the binary checks again, and `okB_sound`, `binOk_of` are theorems.
5. Build it in the package `crate-proofs/` (`FILE` under `crate-proofs/Crates/`, `lake build`
   there, or `lake build Crates.NAME`): it loads the compiled code of `FV.E2E.LinkCheck`,
   `FV.E2E.StackBound`, `FV.E2E.BinCheck` and their imports as a shared library (`fvcheck`, built by Lake from the
   same sources), so `native_decide` runs the checker natively instead of in Lean's interpreter
   (about 15× faster).

What the theorem says, and assumes: e2e.md "Crate-level instance" (the base environment's
contracts, `BaseOk`, are premises; the entry state is a premise as in `backend_correct_program`).
What blocks functions today (blocker list there): nothing on the surveyed crates: every function
of the nine survey crates passes, and all 550 of `examples/fv-demo`'s (with its recursive
function's alias, 551 functions of the program; since agent/sret-purpose, `call_indirect`
requires the callee's parameter purposes to match, so its two `catch_unwind` shims no longer
reach the `sret` vtable methods). Times: under a second per survey crate and 5 s for `fv-demo`
in `link-check`; `lake build` of all ten proofs (`crate-proofs/Crates/`, `fv-demo`'s 551
functions in 18 slices) about 13 s.

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
* `examples/deps`: a crate with real crates.io dependencies from the offline registry
  (`Cargo.lock` committed, `.cargo/config.toml` sets `net.offline`): serde + serde_derive
  (a proc macro, host-built), serde_json, regex, sha2, tiny-keccak, num-bigint, base64, hex,
  hashbrown, indexmap, smallvec, arrayvec, bitflags, byteorder, crc32fast, itoa, ryu, memchr,
  num-traits, rand — 42 dependency packages compiled for the target (and 6 host-only ones:
  serde_derive, proc-macro2, quote, syn, unicode-ident, autocfg). 16 tests check reference
  values (serde_json round trips of a derived struct, regex captures/replace/sets, SHA-2 and
  Keccak/SHA-3 test vectors, big-integer factorials, base64/hex round trips, hashbrown/indexmap
  operations, rand with fixed seeds against the LLVM build's values, …). See *Dependencies*.

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

After agent/atomics-proof stage B (2026-10-02: `atomic_rmw`/`atomic_cas` verified; debug,
`examples/compare.sh` SAME for all three in debug and release): fv-demo 1332 verified of 1346
(8 unverified, 6 fallback), survey 3174 of 3179 (5 unverified), vendor 4381 of 4399
(18 unverified).

After agent/stack-tls-proof stack arguments (2026-10-01: stack-passed parameters and stack-passed
arguments of `call` verified; debug, `examples/compare.sh` SAME for all three): fv-demo 1332
verified of 1346 (8 unverified, 6 fallback), survey 3174 of 3179 (5 unverified), vendor 4395 of
4399 (4 unverified: 3 `tls_value`, 1 stack-passed arguments of a `try_call`).

After agent/stack-tls-proof `tls_value` (2026-10-01: `tls_value` verified, one thread, the
TLSDESC hook contract `TlsOk`; debug, `examples/compare.sh` SAME for all three: fv-demo 19,
survey 53, vendor 189 test outcomes): fv-demo 1336 verified of 1346 (4 unverified, 6
fallback), survey 3174 of 3179 (5 unverified), vendor 4398 of 4399 (1 unverified: stack-passed
arguments of a `try_call`). `lean-e2e-check`: 1148 in scope (1146 before, plus the 2 functions
of `corpus/clif-regress/tls_elf_gd.clif`), 0 rejected, 0 not covered.

After agent/last-unverified (2026-10-01: stack-passed arguments of a `try_call`, `try_call` and
`call_indirect` in `i128`-legalised functions, recursion through the self-call alias;
debug, `cargo fv build --tests`): fv-demo 1340 verified of 1346 (0 unverified, 6 fallback:
`package.metadata.fv.skip`), survey 3179 of 3179, vendor all verified. The last unverified
functions were: the 5 survey `g_u128` test functions (`try_call`s of `i128` functions) and 2
fv-demo `downcast_ref` instances (`call_indirect`), rejected by `Opt.Legal.check`; vendor's
`hashbrown` `reserve_rehash` (a `try_call` of an extern with more than 8 parameters); and
fv-demo's recursive `unwind::deep` (2 instances: a call of a function of the file).
`examples/compare.sh` SAME for all three, debug (fv-demo 19, survey 53, vendor 189 test
outcomes; `cargo fv test`: fv-demo 1340/1346, survey 3179/3179, vendor 4399/4399) and
`--release` (fv-demo 947/953, 6 fallback; survey 2208/2208 — the last 5, release `g_u128`
test functions passing function pointers (`func_addr`) to the harness, are verified since
`Opt.Legal.check` plans `func_addr`; vendor 3082/3082).

Of the verified, `verified (normal returns; unwinding trusted)`: fv-demo 231 / 204, survey
492 / 419, vendor 820 / 727 (debug / release). Before (main fbbd5d9, `try_call` functions
compiled but unverified) survey debug had 2537 verified of 3179. No function is over the
validation budget. `cargo fv test` wall time (a full rebuild of the workspace members, then
the tests under qemu): fv-demo 4 s / 3 s, survey 9 s / 7 s, vendor 16–20 s / 12–14 s (two
runs); plain cg_clif
`cargo test` in a fresh target directory: 0.3 s / 0.3 s, 0.9 s / 1.1 s, 3.6 s / 2.5 s. (Before
the near-linear validator, `lean-backend` ran for over an hour on each of the survey's largest
`try_call` test functions, and the survey build did not finish.)

After agent/trycall-contract (2026-10-02: `CalleeTryOk` satisfiable, the `try_call` payload
defs dead on the normal return; debug, `cargo fv test`): fv-demo 1340 verified of 1346 (6
fallback), survey 3179 of 3179, vendor 4527 of 4527, deps 20821 verified of 21021 (20824
compiled); of them `verified (normal returns; unwinding trusted)`: fv-demo 253, survey 498,
vendor 886, deps 3144. Between agent/callee-fix and agent/trycall-contract, with the `try_call`
functions reported unverified: fv-demo 1087, survey 2681, vendor 3641, deps 17677 verified.
`examples/compare.sh` SAME for all three (fv-demo 19, survey 53, vendor 189 test outcomes).

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

Before agent/fv-deps, a crate with crates.io dependencies (`itoa`, `smallvec`, `crc32fast`;
the dependencies were then compiled by plain cg_clif) also passed (unit tests and a doctest, same outcomes as `cargo test`;
checked with panic=abort).

### Atomics, `bmask`, `fence`, and the vendored real-world crates (agent/fv-fallback)

`atomic_load`/`atomic_store`/`atomic_rmw`/`atomic_cas`/`fence` and `bmask` compile since
agent/fv-fallback: the Cranelift non-LSE lowering (cg_clif's aarch64 flags have `has_lse=0`),
i.e. `ldar`/`stlr` and the `atomic_rmw_loop`/`atomic_cas_loop` LL/SC pseudo-instructions
(`ldaxr`/`stlxr` loops over the fixed registers x24–x28), `csetm` for `bmask`, `dmb ish` for
`fence` — all encode-checked byte-for-byte against llvm-mc and differentially executed
against Cranelift-native on the atomic/bmask/fence runtests. All of them are in E and inside
`E2E.backend_correct_final` (single-threaded Arm model, `docs/decisions/arm-model.md`,
"Atomics"; `atomic_rmw`/`atomic_cas` since stage B). The stack-slot allocator rejects the loop
pseudo-instructions (regalloc2, the default, handles their fixed registers).

`examples/vendor` vendors dep-free crates.io crates (`crc32fast`, `itoa`, `memchr`, `hex`,
`bitflags`, `cfg-if`, `once_cell`) plus a `harness` crate with reference-value tests, to
measure and drive out fallbacks on real code. Vendor patches: dev-dependencies pruned,
`quickcheck!` blocks replaced by deterministic LCG `#[test]`s, itoa's optional `no-panic`
dependency removed, the aarch64-specialized crc32fast tests dropped (their
`stable_arm_crc32_intrinsics` cfg was not set under `cargo fv`, which made the test set differ
between `cargo test` and `cargo fv test`; the cause, found in agent/fv-deps, was the build
script's `$RUSTC --version` failing silently, see *Troubleshooting*, now fixed). The `once_cell` `race` module is what exercises
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
  unverified ("tls_value (outside backend_correct)"; verified since agent/stack-tls-proof,
  see above). The lowering is Cranelift's for cg_clif's
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

### Dependencies (agent/fv-deps)

Since agent/fv-deps every crate compiled for the target goes through the Lean backend, not
only the workspace members. In examples/deps, `cargo fv test` compiles 42 dependency packages
with the Lean backend; the 6 host-only packages (the proc macro `serde_derive` with
`proc-macro2`/`quote`/`syn`/`unicode-ident`, and `autocfg`, a build dependency) and every
build script stay plain rustc. A from-scratch `cargo fv test --no-run` of examples/deps
takes about 45–60 s (32 CPUs).

`examples/compare.sh` (LLVM `cargo test` vs `cargo fv test`, test by test) reports SAME for
fv-demo 19/19, survey 53/53, vendor 189/189 and deps 16/16, debug and `--release`, and for
deps also with `--trap-replaced` (debug and `--release`). fv-demo, survey and vendor have no
non-member dependencies (vendor's crates are workspace members), so their numbers did not
change.

Per package (`cargo fv test --no-run`, panic=unwind; units of the same package summed: e.g.
deps-demo's lib, bin and test harnesses, which also hold the monomorphised generic code of the
dependencies they instantiate):

| package | | debug: functions / verified / unverified / fallback | release: functions / verified / unverified / fallback |
|---|---|---|---|
| deps-demo | member | 4056 / 4028 / 0 / 28 | 3713 / 3676 / 0 / 37 |
| aho-corasick | dep | 2063 / 2063 / 0 / 0 | 1268 / 1268 / 0 / 0 |
| allocator-api2 | dep | 17 / 17 / 0 / 0 | 7 / 7 / 0 / 0 |
| arrayvec | dep | 1 / 1 / 0 / 0 | 1 / 1 / 0 / 0 |
| base64 | dep | 142 / 142 / 0 / 0 | 57 / 57 / 0 / 0 |
| bitflags | dep | 74 / 74 / 0 / 0 | 28 / 28 / 0 / 0 |
| block-buffer | dep | 1 / 1 / 0 / 0 | 1 / 1 / 0 / 0 |
| byteorder | dep | 3 / 3 / 0 / 0 | 2 / 2 / 0 / 0 |
| chacha20 | dep | 79 / 79 / 0 / 0 | 35 / 35 / 0 / 0 |
| const-oid | dep | 110 / 110 / 0 / 0 | 42 / 42 / 0 / 0 |
| cpufeatures | dep | 1 / 1 / 0 / 0 | 1 / 1 / 0 / 0 |
| crc32fast | dep | 124 / 124 / 0 / 0 | 80 / 80 / 0 / 0 |
| crypto-common | dep | 1580 / 1580 / 0 / 0 | 544 / 544 / 0 / 0 |
| digest | dep | 3 / 3 / 0 / 0 | 3 / 3 / 0 / 0 |
| foldhash | dep | 29 / 29 / 0 / 0 | 12 / 12 / 0 / 0 |
| getrandom | dep | 97 / 97 / 0 / 0 | 49 / 49 / 0 / 0 |
| hashbrown | dep | 45 / 45 / 0 / 0 | 14 / 14 / 0 / 0 |
| hex | dep | 26 / 26 / 0 / 0 | 4 / 4 / 0 / 0 |
| hybrid-array | dep | 1 / 1 / 0 / 0 | 1 / 1 / 0 / 0 |
| indexmap | dep | 4 / 4 / 0 / 0 | 2 / 2 / 0 / 0 |
| itoa | dep | 47 / 47 / 0 / 0 | 13 / 13 / 0 / 0 |
| libc | dep | 27 / 27 / 0 / 0 | 11 / 11 / 0 / 0 |
| memchr | dep | 245 / 245 / 0 / 0 | 106 / 106 / 0 / 0 |
| num-bigint | dep | 1051 / 1024 / 0 / 27 | 626 / 610 / 0 / 16 |
| num-integer | dep | 235 / 208 / 0 / 27 | 90 / 77 / 0 / 13 |
| num-traits | dep | 74 / 60 / 0 / 14 | 34 / 32 / 0 / 2 |
| rand | dep | 318 / 302 / 0 / 16 | 182 / 182 / 0 / 0 |
| rand_core | dep | 10 / 10 / 0 / 0 | 0 / 0 / 0 / 0 |
| regex | dep | 429 / 429 / 0 / 0 | 638 / 638 / 0 / 0 |
| regex-automata | dep | 5039 / 5039 / 0 / 0 | 3673 / 3671 / 0 / 2 |
| regex-syntax | dep | 3015 / 3015 / 0 / 0 | 2025 / 2025 / 0 / 0 |
| ryu | dep | 61 / 55 / 0 / 6 | 12 / 10 / 0 / 2 |
| serde | dep | 123 / 121 / 0 / 2 | 98 / 97 / 0 / 1 |
| serde_core | dep | 236 / 228 / 0 / 8 | 177 / 170 / 0 / 7 |
| serde_json | dep | 1177 / 1127 / 0 / 50 | 721 / 689 / 0 / 32 |
| sha2 | dep | 222 / 212 / 2 / 8 | 168 / 161 / 2 / 5 |
| smallvec | dep | 15 / 15 / 0 / 0 | 8 / 8 / 0 / 0 |
| tiny-keccak | dep | 71 / 70 / 1 / 0 | 38 / 38 / 0 / 0 |
| typenum | dep | 12 / 12 / 0 / 0 | 5 / 5 / 0 / 0 |
| zmij | dep | 158 / 147 / 0 / 11 | 98 / 91 / 0 / 7 |
| **your crate(s)** | | 4056 / 4028 / 0 / 28 | 3713 / 3676 / 0 / 37 |
| **dependencies** | | 16965 / 16793 / 3 / 169 | 10874 / 10785 / 2 / 87 |
| **total** | | 21021 / 20821 / 3 / 197 | 14587 / 14461 / 2 / 124 |

Reasons, by count (debug / release):

| reason | your crate(s) | dependencies |
|---|---|---|
| fallback: `unsupported: type f64` / `f32` (floats: serde_json, ryu/zmij float formatting, num-traits/num-bigint float conversions, rand's float distributions) | 28 / 37 | 159 / 78 |
| fallback: `unsupported: type i64x2` / `i32x4` (NEON SIMD: sha2's `vsha256*`/`vsha512*` intrinsics and `aarch64_sha2::compress`, zmij `to_bcd_4x4`) | — | 9 / 6 |
| fallback: `unsupported: opcode f64const` (serde_json `parse_exponent_overflow`) | — | 1 / 1 |
| fallback: `` `iconcat.i64 …` is not in E `` (regex-automata `meta::wrappers::…::new`, release: the function has `i128` values *and* atomics, which `Opt.Legalize128` does not legalise — "legalize128: atomics are not legalised" — so the backend sees the raw `iconcat`) | — | 0 / 2 |
| unverified: validation budget (`sha2::sha{256,512}::soft::unroll::compress_block`, debug also `tiny_keccak::keccakf::keccakf`: fully unrolled rounds) | — | 3 / 2 |

All of these are the hard cases (floats, SIMD, i128 together with atomics, the validation
budget guard); no cheap unsupported construct was left. Every other dependency function is
verified (`E2E.backend_correct_final`; `try_call` functions for their normal returns).

**The dependencies' Lean code runs.** Each executable's `exe` line attributes its functions
through the link map. Debug, `tests/crates.rs`: 21682 functions, 19808 Lean-compiled (members
3052, dependencies 16756, e.g. regex-automata 5039, regex-syntax 3015, aho-corasick 2063,
crypto-common 1580, serde_json 1127, num-bigint 1024), 142 cg_clif fallbacks, 1732 prebuilt
(std/core/alloc, compiler_builtins, musl libc). Under `--trap-replaced` (cg_clif's copy of
every Lean-compiled function, members and dependencies, is a trap) the 16 tests pass, and
`scripts/fv-exec-trace.py` on that build's `tests/crates.rs` harness counts the functions the
run executed (debug; release in parentheses):

| crate | Lean-compiled functions executed | other functions executed |
|---|---|---|
| regex-automata | 2421 (1501) | 0 (2) |
| regex-syntax | 1578 (878) | 0 (0) |
| aho-corasick | 870 (370) | 0 (0) |
| serde_json | 420 (134) | 15 (4) |
| num-bigint | 268 (113) | 8 (2) |
| regex | 141 (247) | 0 (0) |
| memchr | 118 (7) | 0 (0) |
| rand | 103 (release: inlined into the harness) | 0 |
| zmij | 82 (53) | 10 (9) |
| sha2 | 73 (62) | 16 (33) |
| tiny-keccak | 59 (27) | 0 (0) |
| crc32fast | 47 (31) | 1 (1) |
| the test harness itself (`crates`) | 1804 (1566) | 22 (23) |
| std (prebuilt) | 0 | 410 (388) |

("other" in a dependency = its float/SIMD fallbacks, e.g. sha2's NEON SHA instructions, which
the CPU qemu emulates has.)

## Limitations

* Target `aarch64-unknown-linux-musl` only. The host is x86_64, so executables run under
  qemu. Linking always uses `rust-lld`.
* Every crate compiled for the target goes through the Lean backend (`--members-only` and
  skip-deps restrict it); std is the prebuilt LLVM one (rebuilding it with `-Zbuild-std`
  would be the way to cover it, not done).
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

## Stock Cranelift compiler-output comparison

`bash scripts/stock-compiler-comparison.sh --out target/stock-comparison-new`
builds the pinned allocator, Lean backend and instrumented stock compiler, runs
validation, then inventories all official Cranelift filetests and compares literal
function code/relocations under their declared settings. Unsupported settings and
unknown execution metadata remain gaps; this does not claim full CI equivalence.
See [STOCK-COMPILER-COMPARISON.md](STOCK-COMPILER-COMPARISON.md) for prerequisites,
the precise contract, retained artifacts, progress tracking and baseline results.

## Troubleshooting

* `no such command: fv`: put `rust/target/release` on `PATH`.
* `… missing (FV_ROOT=…)`: build the named tool (see Install).
* `toolchain … not found`: install the nightly with the component and target (Install, 1).
* `--panic-abort`: a `should_panic` test fails with an exec error: register qemu with
  binfmt_misc (Install, 2).
* `catch_unwind` does not catch or `Drop` does not run during unwinding: the build uses the
  shipped cg_clif (the summary's `panic=` line says which); build the unwinding one (Install, 5).
* A build script that runs `$RUSTC` (libc, crc32fast, serde, …) fails with `libLLVM….so: cannot
  open shared object file`, or silently sets different `cfg`s than under `cargo test`: fixed in
  agent/fv-deps. `cargo fv` started through another toolchain's rustup proxy (a
  `rust-toolchain.toml` above the crate, e.g. this repository's) inherited that toolchain's
  `LD_LIBRARY_PATH`; cargo puts the nightly's `rustlib/<host>/lib` (with a `librustc_driver`
  when `rustc-dev` is installed) first for build scripts, and the nightly rustc then could not
  find its libLLVM. `cargo fv` now puts the pinned toolchain's `lib/` first.
* A function falls back and you want to know why: `cargo fv report --functions`, or
  `target/fv-report.json`. `--keep-temps` keeps the normalised CLIF (`split/`), the
  per-function objects (`o/`) and the merge inputs in `target/fv/<mode>/tmp/<tag>/`.
* A test fails under `cargo fv test` but passes under `cargo test`: bisect with
  `FV_SKIP=<path substring>` / `FV_ONLY=…` (or `FV_SKIP_DEPS=<package>` for a dependency);
  changing them rebuilds every target crate. Then look at
  the function's CLIF and `llvm-objdump -d` of its object in `--keep-temps`. That is how the
  sret mismatch was found.

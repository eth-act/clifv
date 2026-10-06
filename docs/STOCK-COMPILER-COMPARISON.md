# Stock Cranelift / Lean compiler comparison

The integration boundary is the **unrelocated compiled function**, not a fabricated
ELF executable. Stock `compile` tests compile independent functions. Stock `run`
tests prepare a module, compile functions and signature trampolines, then normally
allocate executable memory, resolve relocations and call the functions. We capture
their compiler output before allocation/relocation; we do not execute the tests.

## Reproduce

One command from a fresh checkout builds all three executables, validates the
harness and takes the complete measurement:

```sh
bash scripts/stock-compiler-comparison.sh \
  --out target/stock-compiler-comparison-new --jobs 2
```

Prerequisites: Linux, git, rustup, Python >=3.11, a C/C++ build toolchain, and the
Lean version pinned in `lean-toolchain` (4.34.1). Put `lean` and `lake` on `PATH`,
or set `LEAN_BIN_DIR=/path/to/lean-4.34.1/bin`. The script installs/selects Rust
1.96.0, builds `lean-regalloc --release --locked`, builds `lean-backend`, clones
the pinned Wasmtime source if absent, applies the instrumentation and builds the
stock exporter with `--locked`. No QEMU or external LLVM binutils are needed.
The default memory cap requires a working systemd user session; explicitly set
`FV_COMPARE_MEMCAP=0` on hosts without one (no cap), or change `FV_MEMCAP` (16G).
Build, toolchain and validation logs are retained in `<output>.build-logs/`.
The allocator path is pinned; inherited Rust wrappers/flags/target directories
are not used to build the comparison infrastructure.

## GitHub Actions

Every pull request and every push to `main` runs the full pipeline on
`ubuntu-24.04`, with two comparison workers. A push to `main` writes the job
summary and saves the artifacts; it posts no comment. CI uses `FV_COMPARE_MEMCAP=0`, because a systemd user session is not
required on the hosted runner. The workflow installs the checksum-pinned Lean
toolchain and caches toolchains, Rust downloads, and compiler build outputs.

A green measurement job means that the full inventory was processed and the
report is valid. It does **not** mean compiler equivalence. The CI adapter accepts
the pipeline's expected exit code 1 only with a complete report. Crashes, partial
inventories, missing reference outputs, changed test sources, and failed stock
assertions fail CI. Unsupported Lean settings or operations remain coverage gaps.

The workflow saves the full artifacts and logs for seven days. It writes a job
summary and posts a PR comment with coverage, exact output matches, complete-file
matches, elapsed pipeline time, and sampled runner memory use. Memory includes
the OS and is measured as `MemTotal - MemAvailable` every 0.1 seconds. Pipeline
time includes Rust toolchain setup. It excludes Lean installation and cache
transfers.

After a successful new measurement, the publisher creates the new comment and
deletes the previous marked comment from `github-actions[bot]`. It preserves
human comments and unrelated bot comments. A failed build or comparison leaves
the previous result intact. A stale commit or older run cannot replace a newer
result.

Same-repository PRs publish in a separate job after the measurement succeeds.
Fork builds use read-only permissions. A separate `workflow_run` publisher reads
the small data artifact and posts their comments. It checks out only the default
branch and never executes fork code. GitHub activates that publisher only after
its workflow and script are merged into the default branch.

### Daily change reports

`stock-comparison-nightly.yml` runs at 06:23 UTC and summarizes existing `main`
push measurements in the pinned [daily reports issue](https://github.com/eth-act/clifv/issues/46).
It does not build the compiler again. Collection starts at the last published
digest, or the preceding 24 hours on first setup. Completed failures and
cancellations are reported as measurement gaps; late completions enter the next
digest. Intermediate pushes can be skipped by the measurement workflow's queue,
so reports attribute changes to measured commit ranges, not proven culprits.

The digest compares individual reported function occurrences under the same
input and stock settings. It shows gained/lost exact matches and supported
outputs, added/removed identities, and commit titles and GitHub authors. Changes
to the pinned reference or recorded harness provenance are not directly
comparable. Changed input/settings and nonrepeatable reference stages are
reported separately, not called compiler regressions. Counts measure artifact
agreement, not execution or proof coverage.

Each nightly saves a compact baseline snapshot and detailed report as Actions
artifacts for 90 days, including on quiet nights. The snapshot is uploaded before
the issue cursor advances. Missing/corrupt saved state fails the digest instead
of silently resetting the baseline. Initial measurements whose artifacts have
expired are explicit gaps. Source measurements retain their existing seven-day
artifact retention.

The bot keeps 30 recent digest comments. Before deleting older marked comments
owned by `github-actions[bot]`, it stores their counts, regressions, removed
identities, and attribution links in the issue body and verifies the update.
Human comments and unrelated bot comments are never deleted. If the compacted
body reaches its size limit, deletion stops rather than dropping findings.

The schedule activates only after this workflow is merged into `main`. A
read-only PR job tests collection against real `main` artifacts and uploads a
preview. After merge, `workflow_dispatch` can preview the digest or publish it
with the `publish` input; only runs from `main` can write to the reporting issue.

Use a fresh output directory; if `--out` is omitted a timestamped directory is
chosen. `--input <official-file.clif>` selects a pilot;
the report still retains the complete official inventory and says how many files
were actually processed. `progress.json` records completed files. Each processed
file has a retained `files/<official-path>/result.json` even before the final
`results.json` and `summary.md` are produced. Exit 1 means suite-wide equivalence
has **not** been established, including when code matches but metadata is unknown.

The pinned reference is Wasmtime commit
`46c23a87dac1465986a8ad53ba6a7ae49372857b` (Cranelift 0.136.1).
The exporter dependency versions/sources are checked against the stock lockfile.
The checked-in upstream instrumentation patch, source hashes, binary hashes,
original test files, compilation commands, stdout/stderr and artifacts are retained.
`BLESS` is forbidden, so reference assertions cannot rewrite their expectations.

## Comparison contract

1. Inventory **every official `.clif` file**, including non-runtime tests. Parser,
   verifier, optimizer, CFG and similar tests that do not produce machine code
   are explicitly non-binary; this investigation does not claim to run their
   IR/text assertions. Foreign architecture tests are retained as coverage gaps,
   never retargeted to AArch64. Parser warnings/skips and errors are distinguished.
2. Use the reader and effective settings from the stock filetest framework,
   including `machine_code_cfg_info=true`. No flag overrides or feature-reduced
   configurations are substituted. A missing required ISA is not invented.
3. Capture `compile` output **inside `TestCompile::run`**, keeping its verifier,
   disassembly/filecheck/precise-output assertions and expected-failure handling.
   Each independent function's assertion result is retained; capture continues
   after failures to inventory the remaining functions. Normal stock execution
   would stop that stage at its first failure. A compile test may repeat a
   function name (`isa/aarch64/condops.clif` has 50 functions named `%f`), so
   each function's artifacts are named by its position in the file, and each
   function is compared with its own stock artifact. A run test cannot repeat a
   name: stock `TestFileCompiler` rejects it.
4. For `run`, use the actual `TestFileCompiler` preparation: declarations, hostcall
   substitutions, function renaming and signature trampolines. Compile-only mode
   uses the same compile call as the JIT module, with a memory provider that panics
   on executable allocation or finalization. Supporting trampolines are exported
   but are **not counted as Lean-compiled test functions**.
5. Stock `compile` targets retain their exact declared triple. Stock `run` copies
   requested flags into its execution-host ISA; here AArch64 Linux substitutes
   for that host. CPU-compatibility selection and runtime assertions are not run.
   This reproduces the compilation request for that hypothetical host, **not a
   claim to capture an actual CI job**. Process-address hostcall substitutions are
   flagged; reference exports run twice to detect nondeterministic artifacts.
6. Give Lean the stock-effective CLIF and the complete effective shared/ISA flags
   in an explicit JSON request. Where Lean needs inline signatures instead of
   `sigN` references, the stock reader checks that adaptation preserves the full
   IR (modulo duplicate signature-table IDs). Both forms and their hashes remain
   available. The harness verifies Lean's receipt echoes the exact settings/input
   request; a missing, rejected or altered receipt is never settings agreement.
7. Compare literal code buffers, relocation offset/kind/target/addend, required
   alignment and trap records. Symbol identity conversion removes the CLIF `%`
   prefix; relocation records are compared structurally rather than as JSON text.
   No instruction bytes, padding, immediates, frames or addresses are masked.
   Lean dump bytes/relocations and alignment are also checked against its actual
   relocatable ELF object. There is **no Cranelift ELF** at this boundary, so ELF
   packaging and a later linked executable are not the comparison objects.

## Lean configuration support and proof scope

`lean-backend --stock-config request.json --config-receipt receipt.json` is an
experimental, fail-closed adapter. Unknown, missing, duplicate and unimplemented
settings are rejected explicitly. Supported targets are generic/ELF AArch64 and
AArch64 Linux; optimization is `none`, with no extra enabled ISA features. The
complete policy table lives in `FVTest/Backend/StockConfig.lean`.

`preserve_frame_pointers=false` omits an optional empty leaf frame **before
emission**, checking calls, frame-register usage, incoming stack-argument loads,
spill/callee-save storage and explicit frame storage. Required frames remain.
`is_pic=false` rejects functions needing the currently fixed GOT/far-symbol
lowering; it does not silently compile those as PIC. `tls_model=none` rejects
functions needing the existing fixed TLSDESC lowering. `unwind_info=false` removes
unwind emission. Unsupported configurations are not weakened to improve results.

This adapter is **not covered by `backend_correct`**. Configured compilations are
explicitly marked unverified; register allocation retains its existing checker.
The original fixed-configuration compiler/proof path is unchanged. Equal output
is empirical evidence, not a Lean proof of equivalence to stock Cranelift.

## What counts as agreement

`exact_code_artifact` requires identical machine bytes, relocations, alignment and
traps, an accepted configuration contract, repeatable stock artifacts, and Lean
dump/object consistency. Missing output or unsupported settings are gaps, not
agreement. A file is credited only if **every test function in every declared
AArch64 binary-producing stage** meets that contract.

`full_artifact_equivalence_verified` additionally requires all execution metadata.
Currently unwind absence can be checked when disabled and empty stack maps can
be checked, but there is **no equivalent Lean export of Cranelift's exception
tables/regular-call records**. Enabled unwind metadata is also not compared fully.
These fields are unknown, not equal: full artifact equivalence is currently false.

Expected compile failures produce no binary; their stock assertion results are
retained, but Lean rejection equivalence is not yet tested. Cross-host CPU gating,
stock JIT execution with Lean artifacts, reference trampoline agreement and all
non-AArch64 backends remain outside current coverage.

## Baseline and next work

The current full baseline is `target/stock-compiler-comparison-final/`.
Its `summary.md` gives file-level coverage and function-output counts. Function
counts repeat when a test declares multiple ISA/settings variants or compilation
commands; they are not additional official test files or runtime assertions.

The first settings-matched baseline inventoried all 1,302 files: 484 have an
AArch64 binary-producing stage, 630 have no supported Lean target, 180 are
non-binary, and 8 are stock parser-warning skips. Lean received compilation
requests for 483 files; 118 produced test functions that could be compared.
451 function outputs match code bytes, relocations, alignment and traps; all
declared AArch64 test-function code artifacts match in 19 files. (The first
published count, 425, compared every function of a repeated name with one of
them.) None is credited as full execution-metadata equivalence. Stock compile
assertions all pass.
`runtests/throw.clif` has nonrepeatable reference artifacts because stock preparation
substitutes a process-local host function address; it is not credited as agreement.

Next, implement a comparable exception/unwind metadata export, capture the exact
target/CPU eligibility of a selected real CI host, and feed matched Lean artifacts
to the stock loader/trampolines. Add backend functionality for the explicitly
rejected settings/functions without substituting easier configurations.

`prejit-baseline.py` is retained for stock-exporter validation and historical
diagnostics; it does not give Lean a stock-settings contract. Use the single
pipeline above, not that diagnostic script, for the settings-matched baseline.

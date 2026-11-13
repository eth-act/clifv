# Stock Cranelift / Lean compiler comparison

The integration boundary is the **unrelocated compiled function**, not a fabricated
ELF executable. Stock `compile` tests compile independent functions. Stock `run`
tests prepare a module, compile functions and signature trampolines, then normally
allocate executable memory, resolve relocations and call the functions. We capture
their compiler output before allocation/relocation; we do not execute the tests.

## Two parity metrics

This comparison is one of the two stock-parity metrics. Both count (`AGENTS.md`).

| | Filetest comparison (this document) | Crate parity |
|---|---|---|
| Input | every function of Cranelift's own filetests, under their declared settings | every function of real Rust crates that cg_clif compiles (one default setting) |
| A function that Lean does not compile | counts as a miss | almost none occur |
| What it rewards | coverage and identical output (SIMD, tail calls, floats, settings) | identical output on ordinary Rust code |
| Where it runs | CI, on every PR and main push | the full gate on `main` (fv-demo, survey); by hand for a PR: `scripts/stock-crate-parity.py` (`docs/USAGE.md`) |
| Where it is reported | PR comment; daily digest (#46) | daily digest (#46); cause analysis in #557 |

A parity PR reports both results and loses no match on either.

The filetest comparison reports two counts. **Exact function outputs** are measured through the
stock-configured driver (`--stock-config`), which runs unproved steps after allocation (the frame
decision, `argLoadsFromSp`, `dropDeadNotrapLoads`, native `i128`). The **honest metric** counts
the outputs of the proved compiler, with the test's settings as compiler input and no unproved
step, that are identical to stock for functions `backend_correct` covers ("The honest metric"
below). Both have a lost-match check.

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
toolchain and caches toolchains, Rust downloads, and Rust build outputs.

### Lean executables in CI

The job does not build Lean from nothing (#1018). The four Lean executables the
pipeline runs (`LEAN_EXES` in `scripts/stock-compiler-comparison.sh`) import 418
of the tree's modules. A plain `lake build` of them on one hosted runner (16 GB,
no swap, one `lean` per core) lost the runner or ran out of time after every
Lean source change. Instead:

1. `scripts/stock-comparison-lean-build.py` picks a Full gate build
   (`.github/workflows/full-gate.yml`, artifact `lake-full`): the one of the
   tested commit if there is one, otherwise the complete, unexpired one that
   leaves the fewest recorded seconds of those 418 modules to build (a module
   whose source differs from that build's commit, and its importers). After a
   squash merge this is usually the build of the pull request's head, which has
   the same tree. Only runs of the Full gate workflow in this repository count,
   never a `pull_request` run, and only a build whose assemble job succeeded (a
   run that is still assembling, or published a partial build, is passed over).
2. `.github/actions/fv-lean` unstages that build and the workflow's own saved
   outputs (Actions cache `stock-lean-*`) into the Lake cache. Lake's cache is
   keyed by each module's inputs, so an older or unrelated build is safe: Lake
   restores a module only when its source, its imports, the toolchain and the
   Lake configuration match. No module of the 418 reads a file while it
   elaborates (`scripts/test_stock_comparison_lean_build.py` checks this).
3. `.github/scripts/stock-comparison-lean.sh` builds what is left with
   `scripts/lake-serial-build.py` under the limits of the Full gate's shards
   (swap, heavy modules alone), within `STOCK_LEAN_LIMIT_S` (150 minutes; 293 of
   the 418 modules took 31 minutes when measured). It saves the result for later runs;
   after a failure or the time limit it saves the modules that did build, so a
   re-run continues from them.
4. The pipeline then runs with `FV_COMPARE_PREBUILT=1`: an executable that is
   out of date is an error there, not a build.

A pull request that changes Lean sources is measured before its own Full gate
run exists, so its changed modules and their importers are built in step 3;
when only the lookup itself fails (an API error), the job fails rather than
building everything.

**No result is a failed check.** A measurement that fails, runs out of time
(`STOCK_LEAN_LIMIT_S`, `STOCK_COMPARE_LIMIT_S`) or loses its runner fails
**Build and compare** with an error annotation titled `No stock-comparison
result`, and **Check lost matches** fails with the same title instead of being
skipped (a skipped check reads as "nothing lost"). The label
`stock-comparison-accept-losses` does not override it. Re-run the failed jobs
(`gh run rerun <run> --failed`). **Check lost matches** runs after a cancelled
measurement too (cancelled by hand, at the job's 300-minute limit, or because
a newer commit or event of the pull request started another run) and fails in
the same way; when another run replaced it, that run's result is the one that
counts, otherwise re-run all jobs (`gh run rerun <run>`: `--failed` re-runs
failed jobs and the jobs that need them, which after a cancelled measurement is
the check alone). A pending push run of `main` that GitHub drops from the queue
for a newer push starts no job at all.

Measured: on #1019's first run (the chosen build had the tested tree's Lean
sources: nothing to build) the job took 10 minutes, 4 of them the download and
unstaging of `lake-full`, 1 restoring and staging the executables, 3 the Rust
builds and the comparison; from the workflow's own cache, 6 minutes. With a
change at the bottom of the import cone (#1020, a scratch declaration in
`FV/Clif/Syntax.lean`: 293 modules to build on the runner) the job took 41
minutes: 29.2 for the scheduler (3,012 s of Lean, heaviest module 9.4 GB),
2 for the link and the stage, 4.5 for the Rust builds and the comparison.

A green measurement job means that the full inventory was processed and the
report is valid. It does **not** mean compiler equivalence. The pipeline exits
with 10 when a measurement finished; the CI adapter accepts only that code, and
only with a complete report. Crashes, partial inventories, missing reference
outputs, changed test sources, and failed stock assertions fail CI. Unsupported
Lean settings or operations remain coverage gaps.

### Lost matches

The run summary lists every exact output as (test, variant, stage, position of
the function in the variant, function name). The position matters: a test file
can repeat a function name. Before measuring, CI finds a baseline: the newest
push run on `main` whose commit is an ancestor of the tested commit and that
saved a summary (`scripts/stock-comparison-baseline.py`). A pull request is thus
compared with the `main` commit it is based on, not with a newer `main`. The
summary records the outputs gained and lost since that baseline.

The **Check lost matches** job (`scripts/stock-comparison-ratchet.py`) fails
when an output that matched on the baseline no longer matches, in either metric
(the summary's `matched` and `proved_matched`; a baseline from before the honest
metric compares the exact outputs only). If the loss is
intended, add the label `stock-comparison-accept-losses` to the pull request and
re-run that job; the label is read when the job runs. A push to `main` has no
override: the commit is marked failed, and the next push compares with it. A
missing baseline (no measured ancestor yet, or one whose summary has another
format) is reported, not failed. A baseline that exists but could not be
retrieved or read (an API error, a damaged or malformed summary, a shallow
checkout) fails the job, and the label does not override that: without the
baseline, lost matches cannot be ruled out. Re-run all jobs of the workflow run.

The summary also hashes the files that do the measuring (the comparison
scripts, the stock exporter and its patch, `FVTest/Backend/StockConfig.lean`,
`FVTest/Backend/Main.lean` and this workflow; `HARNESS` in
`scripts/stock-comparison-ci.py`). The comment names the ones that changed
since the baseline, because a gain there can come from the measurement rather
than the compiler. Summary artifacts from `main` are kept for 90 days, so that
later runs can use them as baselines.

The workflow saves the full artifacts and logs for seven days. It writes a job
summary and posts a PR comment with coverage, exact output matches, complete-file
matches, setting and operation rejections, the gains and losses since the `main`
baseline, elapsed pipeline time, and sampled runner memory use. Memory includes
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
the small data artifact and posts their comments, also when only the lost-match
job failed. It checks out only the default branch and never executes fork code.
GitHub activates that publisher only after its workflow and script are merged
into the default branch.

### Daily change reports

`stock-comparison-nightly.yml` runs at 06:23 UTC and summarizes existing `main`
push measurements in the pinned [daily reports issue](https://github.com/eth-act/clifv/issues/46).
It does not build the compiler again. Collection starts at the last published
digest, or the preceding 24 hours on first setup. Completed failures and
cancellations are reported as measurement gaps; late completions enter the next
digest. Intermediate pushes can be skipped by the measurement workflow's queue,
so reports attribute changes to measured commit ranges, not proven culprits.

Each digest is one table: the rows of the PR comment, with the change since the
previous digest in each row. Below it, the digest names lost exact matches with
the measured commit range where each was first seen. Matches are compared per
reported function occurrence under the same input and stock settings; changed
input/settings and nonrepeatable reference stages are not called losses. The
digest also names `main` commits whose measurement could not be compared, and
measurements where the pinned reference or recorded harness changed, which are
not directly comparable. The report artifact keeps the per-measurement detail:
gained and lost matches and supported outputs, added/removed identities, commit
titles and GitHub authors. Counts measure artifact agreement, not execution or
proof coverage.

The digest also reports crate parity, the second metric. The full gate's
`cargo fv` job runs plain `cargo fv test --keep-temps --no-run` on `examples/fv-demo`
and `examples/survey` and `scripts/stock-crate-parity.py` on the kept objects, and
uploads the per-function result as the artifact `crate-parity-<crate>-<attempt>`
(90 days). The step is a measurement: it runs whether or not the gate's own
`cargo fv` line passes, and it never changes the job's result. The digest reads
the newest full-gate run on `main` that has both artifacts and shows one more
table: byte-identical functions per crate, with the change since the previous
digest. It names functions that stopped matching, by name with the localising
`__fv_<cgu>_` prefix removed, counting a function that Lean no longer compiles as
lost too. A full-gate run without the artifacts is passed over and never resets
the crate baseline. Full-gate runs are post-merge and can be hours apart, so a
digest can repeat the previous crate measurement; it says so.

Each nightly saves a compact baseline snapshot and detailed report as Actions
artifacts for 90 days, including on quiet nights. The snapshot is uploaded before
the issue cursor advances. Missing/corrupt saved state fails the digest instead
of silently resetting the baseline. Initial measurements whose artifacts have
expired are explicit gaps. Source measurements retain their existing seven-day
artifact retention.

The bot keeps 30 recent digest comments. Before deleting older marked comments
owned by `github-actions[bot]`, it stores their counts, lost matches and their
attribution links in the issue body and verifies the update.
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
`results.json` and `summary.md` are produced. Exit 10 means the measurement
finished and suite-wide equivalence has **not** been established, including when
code matches but metadata is unknown. Any other nonzero exit is a failure.

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
AArch64 Linux; optimization is `none`. The complete policy lives in
`FVTest/Backend/StockConfig.lean`.

Some settings change stock's code only for some functions. Lean accepts such a
setting for a function only if the setting cannot change that function's code.
Each other function is rejected for that setting. Lean records it in the receipt's
`function_rejections`, and the report counts it as `unsupported_configuration`.
References are to `cranelift/codegen/src` at the pinned commit.

| Setting (when `true`) | What it changes in stock code | Lean accepts it for |
| --- | --- | --- |
| `enable_llvm_abi_extensions` | `f128` parameters of `apple_aarch64` signatures (`isa/aarch64/abi.rs:231`) | Every function: Lean has no float types and does not lower `apple_aarch64` |
| `enable_multi_ret_implicit_sret` | Returns that do not fit in registers (`isa/aarch64/abi.rs:382`, `machinst/abi.rs:936`) | Every function: Lean rejects more than 8 returns |
| `has_fp16`, `has_dotprod`, `has_i8mm` | Float and vector lowering rules only (`isa/aarch64/inst.isle`, `isa/aarch64/lower.isle`) | Every function: Lean's CLIF has integer types only |
| `has_lse` | `atomic_cas`, and `atomic_rmw` except `nand`/`xchg` (`isa/aarch64/lower.isle:2328-2388`) | Functions without those instructions |
| `use_csdb` | `select_spectre_guard` and the `br_table` sequence (`isa/aarch64/lower.isle:2274`, `isa/aarch64/inst/emit.rs:3276`) | Functions without those instructions |
| `sign_return_address`, with `sign_return_address_with_bkey` and `has_pauth` | Signs the return address of each function with a frame (`isa/aarch64/abi.rs:1365`) | Functions without a frame; none if `sign_return_address_all` is also set |
| `use_bti` | Adds `bti c` to every function (`isa/aarch64/abi.rs:638`) | No function: the whole request is rejected |

If a function is not signed, `sign_return_address_all`, `sign_return_address_with_bkey`
and `has_pauth` have no effect on it. Lean's frame decision stands in for
stock's, and the comparison checks it against stock's code: if stock signed a
function that Lean accepted (stock sets up a frame where Lean has none), the
function is counted as `unsupported_configuration`, not as a difference.

`preserve_frame_pointers=false` omits an optional empty leaf frame **before
emission**, checking calls, frame-register usage, incoming stack-argument loads,
spill/callee-save storage and explicit frame storage. Required frames remain.
`is_pic=false` rejects functions needing the currently fixed GOT/far-symbol
lowering; it does not silently compile those as PIC. `tls_model=none` rejects
functions needing the existing fixed TLSDESC lowering. `unwind_info=false` removes
unwind emission. Unsupported configurations are not weakened to improve results.

Before allocation, the adapter drops each `notrap` load whose results are unused
(`StockConfig.dropDeadNotrapLoads`, #970), as stock does
(`must_lower_even_if_unused`, `inst_predicates.rs:113`). This pass is unproved.
The CLIF fact it relies on is `Clif.evalInst_notrap_load`: such a load reads
without changing memory, or the run is stuck; it never traps. Trapping, atomic
and incoming stack-argument loads stay. The default mode and `cargo fv` keep these
loads, as cg_clif's Cranelift 0.136.1 does.

This adapter is **not covered by `backend_correct`**. Configured compilations are
explicitly marked unverified; register allocation retains its existing checker.
The original fixed-configuration compiler/proof path is unchanged. Equal output
is empirical evidence, not a Lean proof of equivalence to stock Cranelift.

## The honest metric

`lean-backend --settings request.json --settings-receipt receipt.json` is the proved
settings mode: the request (the `--stock-config` schema) is compiler input, and the proved
compiler (`cargo fv`'s default mode: regalloc2 checked by `checkAlloc`, dead cleanup, no
`--opt`) compiles every function exactly as without the option. No stock-configured step runs:
no `StockConfig.configure`, `argLoadsFromSp`, `dropDeadNotrapLoads` or `I128Native`.
Settings the proved compiler does not implement reject the request (exit 3), as with
`--stock-config`, or per function the function's output (`StockConfig.admit`: the checks of
the table above); such a function stays compiled, because its callers' code does not depend on
it. `preserve_frame_pointers` is compiler input: without it, a leaf that needs no frame is
compiled without one (`Backend.frameless`, stock's decision `Backend.frameRequired`,
`isa/aarch64/abi.rs:1265`); no end-to-end theorem covers a frameless leaf yet (#1028), so such a
function is reported unverified. The receipt's `functions` gives per function
`setting_rejection`, `unsupported`, or `backend_correct` (with `unverified`/`unvalidated`: why
not). `--opt`, `--regalloc`, `--personality`, `--pipeline-t` and `--stock-config` are refused.

`scripts/stock-compiler-compare.py` compiles every compilation group a second time in this mode
(`--proved-compiler`, default `lean-backend`) and stores per function a compact `proved` row:
its status as `compare_function` decides it, `backend_correct`, and `honest` (identical and
covered). The totals give `proved_exact_code_artifacts` and `proved_function_statuses`
(`identical_code_artifact_not_covered`: identical, outside `backend_correct`). CI fails on a
failed proved compilation, as on a failed stock-configured one.

First value: 76 of the 4,455 stock outputs at `41e51746d` (all 76 are among the 1,970 exact
outputs). Of the others, 1,793 are leaves rejected for `preserve_frame_pointers=false`, 108 are
identical but outside subset E, and 20 differ (#44, thread C).

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

The per-function settings policy above changes these counts. Of the 4,455 stock
outputs, 465 match (was 451) and 1,145 differ (was 952). 432 are rejected for a
setting (was 1,176) and 2,413 for an operation Lean does not support (was 1,876).
Compared outputs now come from 151 files (was 118). Every output that matched
before still matches. The remaining setting rejections are mostly
`opt_level=speed` or `speed_and_size` (243), `has_lse` atomics (114),
`is_pic=false` far symbols (40) and `use_bti` (11).

Next, implement a comparable exception/unwind metadata export, capture the exact
target/CPU eligibility of a selected real CI host, and feed matched Lean artifacts
to the stock loader/trampolines. Add backend functionality for the explicitly
rejected settings/functions without substituting easier configurations.

Experimental schedule diagnostics require `lean-backend-lowering-trace INPUT.clif OUTPUT.json --stock-schedule`. The ordinary diagnostic invocation avoids constructing the experimental schedule and its full-state snapshots. Replay checks equality with deterministic reexecution; it does not establish semantic correctness or equivalence to stock.

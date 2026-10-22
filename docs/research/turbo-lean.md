# turbo-lean: evaluated, not adopted (2026-10-22)

Question: can [Th0rgal/turbo-lean](https://github.com/Th0rgal/turbo-lean) replace stock Lean
v4.34.1 for clifv's builds? Evaluated at turbo-lean commit
[`a8e2269`](https://github.com/Th0rgal/turbo-lean/commit/a8e2269) (2026-10-22) against clifv
`77c949a2`. Answer: **no.** It is not a Lean build. Its `build` command runs the project's own
`lake build`, so cold module builds take as long as before. Its fast paths are caches, and
per-theorem checks against `sorry`-stubbed prefixes, which a gate cannot accept as a module proof.

## What it is

- A Rust command-line tool (~37k lines, `crates/turbo-lean`) plus a small Lean library
  (`lean/TurboLean`: the in-memory "Zygote" worker, axiom inspector, specs; its own
  `lean-toolchain` is v4.31.0). It is **not** a fork of Lean. It patches nothing upstream and ships
  no toolchain or elan channel. It runs the toolchain the project pins (`detect_toolchain` reads
  `lean-toolchain` and looks it up under `~/.elan/toolchains`).
- `turbo-lean build [targets]` (`lake_build.rs`, `run_build`): it hashes the project's sources
  and checks its own SQLite + BLAKE3 content-addressed store. Several agents asking for the same
  build share one run (`flock`). On a hit, it hard-links the artifacts into `.lake/build`. On a
  miss, it runs **`Command::new("lake").arg("build")`** with the given targets (it only adds
  `LEAN_STACK_SIZE_KB`), then copies or hard-links every `.olean/.ilean/.c` into its store
  ("ingest").
- `turbo-lean check FILE --decl X`, `agent-step`, `pr-verify`, `ci-verify`: these split a file
  into theorem "shards". To check one theorem, it elaborates the file prefix with every earlier
  theorem replaced by `:= sorry`, then the theorem itself, in a resident worker process that
  keeps `Command.State` warm. Verdicts are cached by hash, and a hit returns "verified" without
  rechecking. A gate blocks `sorryAx`, `Lean.ofReduceBool`/`native_decide`, `trustCompiler`,
  `extern`/`implemented_by`, `unsafe` and unknown axioms. The tool also pins theorem statements
  and signs "receipts".
- Also included: `fast-check` (CPU/GPU counterexample search via lean-native), `eval` (a warm
  `lean file.lean` for `#eval` drivers), cache sync and serving, and an MCP server.
- Claimed speedups (README, `autoresearch/VERITY_BENCHMARK.md`) are for re-checking one edited
  theorem (2–30 ms warm instead of a 3.6–10 s `lake env lean` of the file) and for cache hits.
  The repo reports no cold-build speedup, and the tool has no mechanism for one.

## Trust impact

- **Kernel, type checker, `ofReduceBool`, proof-skipping options: untouched.** No Lean source is
  modified. `debug.skipKernelTC` and `addDeclWithoutChecking` are never used. Its Lean code adds
  declarations with `Lean.addDecl` or `IO.processCommands`, so the stock kernel checks them.
- **`turbo-lean build` = stock `lake build`.** The `.olean`s come from the same `lean` binary, so
  a turbo-lean build carries the same trust as a stock one. Its cache-hit path is a second
  artifact cache, in the same trust class as Lake's (`FV_LAKE_CACHE`).
- **`check`/`pr-verify` verdicts are not module proofs.** A shard is checked against a prefix in
  which the earlier theorems are `sorry`. Cached verdicts are trusted without rechecking. Such a
  verdict cannot replace `lake build` plus the axiom audits. Its gate also rejects
  `native_decide`, which clifv's non-vacuity witnesses are allowed to use, so
  `ci-verify --mode untrusted` would reject clifv modules that are fine.
- A stock-Lean final check would remain possible: the main gate already runs stock
  `lake build` + `scripts/axiom-audit.py`. It did not come to that, because nothing is adopted.

## Compatibility with v4.34.1

There is nothing to rebase. The tool drives whatever toolchain the project pins. Its Zygote
worker (`ZygoteWorker.lean`) is compiled on first use with the project's own `lean -c` +
`leanc`. Under v4.34.1 this worked: `check --decl` verified theorems in a toy project and in
`FV/Backend/Proof/IselShpOracle.lean`. One splitter problem showed up: a theorem preceded by
`set_option … in` (`oracle_ctl`) was not found ("found 23 theorem shards"; the file has 24).

## Measurements (same commit, same caps, run at the same time)

Setup: two scratch worktrees under `/mnt/storage/turbo-lean/` at `77c949a2`, each with a
private copy of `.lake` (no shared-cache writes during the runs). For each module, both
worktrees deleted that module's outputs. Then, simultaneously, A ran
`scripts/memcap.sh lake build M` and B ran `scripts/memcap.sh turbo-lean build M`, with the
same `FV_MEMCAP` and `LEAN_NUM_THREADS=2`. Wall time, CPU time and peak RSS come from
`/usr/bin/time -v`. The machine was shared and heavily loaded (module times were 1.4–4.3× the
recorded ones), and both sides saw the same load. Rebuilding `IselTermFactsCall` produced a
different `.olean` (see below), so `DefGenTab` rebuilt 30 modules on both sides, including
`KillTab` (about 1,930 s).

| Module | wall stock (s) | wall turbo (s) | Δ | CPU stock (s) | CPU turbo (s) | peak stock (GiB) | peak turbo (GiB) |
|---|---|---|---|---|---|---|---|
| StockCmpWithFlags | 6 | 52 | +46 s | 6 | 37 | 2.01 | 2.01 |
| IselTermFactsCall | 3009 | 3059 | +1.7% | 1822 | 1861 | 1.85 | 1.90 |
| DefGenTab (+29 upstream) | 4014 | 4046 | +0.8% | 2988 | 3036 | 2.82 | 2.74 |
| IselSzTab | 2244 | 2513 | +12.0% | 1833 | 1905 | 2.05 | 1.88 |
| IselCtlTry | 1612 | 1628 | +1.0% | 1166 | 1179 | 1.69 | 1.70 |
| StockNoOpportunityTable | 292 | 327 | +11.9% | 187 | 225 | 13.16 | 13.15 |
| RuleArith | 654 | 688 | +5.2% | 6818 | 6783 | 15.49 | 15.46 |
| **total (7 paired)** | **11830** | **12311** | **+4.1%** | **14819** | **15025** | | |
| RuleBitops7 | killed¹ | 787 | | | 4012 | | 17.63 |

¹ The stock run was killed by systemd-oomd during a machine-wide memory-pressure event (global
OOM kills at 05:31), not by its own cap. A rerun was not possible while the machine had under
10 GB available.

- Lean's own per-module timings (`Built M (Ns)`) match within noise in both directions
  (IselCtlTry 1611/1523 s, RuleArith 653/584 s, IselSzTab 2243/2475 s). turbo-lean adds a fixed
  ~35–50 s per invocation (hashing the project, ingesting 1,458 artifacts) and nothing else.
- **Outputs are the same.** 5 of the 7 rebuilt `.olean`s are byte-identical between stock,
  turbo-lean and the shared cache. `IselTermFactsCall` and `IselCtlTry` differ in bytes between
  *any* two builds, stock against stock included: their `.olean` output is not deterministic. A
  dump of every constant in the 8 rebuilt modules (22,322 constants: name, statement hash,
  axioms, using a memoised traversal that matches `Lean.collectAxioms` exactly) is identical
  between the stock and turbo-lean builds. The axiom sets seen are `[]`, `[propext]`,
  `[Quot.sound, propext]` and `[Classical.choice, Quot.sound, propext]`.
- No full FV build was run under turbo-lean. Its build path executes the same `lake build`, and
  the sample shows only the fixed overhead, so a full build (~26 h CPU per side) would add no
  information.
- The dev loop with `check` (IselShpOracle, theorem `cas_ok`): `lake env lean` on the whole file
  took 34 s. The first `check --decl` took 26 s (6.3 s import + 19.4 s elaboration of the prefix
  and shard). An unchanged re-run took 0.03 s (cached verdict). After a one-line proof edit, a
  warm re-check took 9.5 s (0 s import, 9.3 s to elaborate the theorem). This is real, but it
  only speeds up elaboration of the one theorem and needs `sorry`-stubbed prefixes; the
  language server's incremental elaboration gives a similar loop.

## Side effects relevant to the shared machine

- `check` leaves a detached `turbo-lean serve` + `turbo_zygote` daemon listening on
  localhost. One was still running 4.6 h later, with a 535 MB worker holding the clifv
  environment. Its working state lives in `/dev/shm/turbo-lean-staging-<uid>` (RAM).
- If a worktree has no `.lake/build/lib`, `build` hard-links the *main clone's* `.lake` into
  it (`lake_build.rs`, "auto worktree hardlink"). This bypasses clifv's `FV_LAKE_CACHE` scheme.
  Ingest also sets `.lake/build` files to mode 0444, and those files are hard links into the
  shared Lake cache.
- `mcp` and `fast-check` send telemetry to `https://telemetry.thomas.md` by default
  (`TURBO_LEAN_TELEMETRY=off` disables it).

## Decision

Keep stock Lean v4.34.1 and the current Lake cache + `scripts/lake-serial-build.py`. turbo-lean
has no toolchain to switch to. Its build is stock `lake build` plus ~4% overhead. Its fast
paths are caching (clifv already has one) and sorry-prefixed per-theorem checks, which cannot
serve as gate evidence. Our build time is dominated by kernel checking of single large
declarations (`decide +kernel`/`rfl` over generated ISLE data, `bv_decide`). This tool does not
address that, and neither did the "fast-lean" toolchain evaluated earlier (BuildAccel).

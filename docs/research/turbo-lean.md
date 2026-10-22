# turbo-lean: evaluated, not adopted (2026-10-22)

**Update (agent features re-evaluated, 2026-10-22, turbo-lean `ded00b8`, clifv `5c1351a0`):**
see [Agent features](#agent-features-re-evaluated). The per-theorem edit loop
(`check --decl`) works on our heavy proof modules. It is a large win when an agent edits a
cheap theorem inside an expensive file: 0.04–1.3 s per edit instead of a 16–28 min module
rebuild. It stays a dev-loop tool (`docs/USAGE.md`, "Fast proof-edit loop"). Singleflight, the
memory governor and statement pinning are of no use to us.

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

## Agent features re-evaluated

Setup: worktree at clifv `5c1351a0`, dependencies restored from `FV_LAKE_CACHE`, turbo-lean
`ded00b8` built with `cargo build --release` (its build script first needs `lake build` in
`lean/`). Each sequence ran in one `scripts/memcap.sh` scope (`FV_MEMCAP=24G`,
`LEAN_NUM_THREADS=2`) with a fresh `TURBO_LEAN_HOME` and no daemons running. Peaks are the
scope's cgroup `memory.peak`, which includes the daemons. The machine was shared and loaded.

### 1. Edit loop: `turbo-lean check <file> --decl <id>`

"lake" means `lake build M` after a comment-only edit to `M`, with dependencies cached. Edits:
`skip` inserted as the first tactic, then `skip; skip`. "broken" means `exfalso` inserted as the
first tactic.

| Module (theorem) | lake build M | cold check | unchanged | edit 1 / edit 2 | broken | scope peak |
|---|---|---|---|---|---|---|
| KillTab (`nop_rhs`) | 1,697 s | 1.47 s | 0.01 s (cache) | 0.11 / 0.11 s | rejected, 4.4 s, Lean error | 4.5 GB |
| IselShpTry (`handOk_try`) | 1,658 s | 2.43 s | 0.02 s | 1.31 / 1.12 s | rejected after the 30 s timeout, no Lean error | 4.4 GB |
| IselCtlTry (`tryRulesCorrectP`, has `have`s) | 952 s | 1.31 s | 0.01 s | 0.04 / 0.05 s | rejected, 3.8 s, Lean error | 3.5 GB |
| FVTest SpillInstCheckCompleteW (`opsOkB_iRets`) | ~1.3 s | 4.99 s | 0.01 s | 0.10 / 0.09 s | rejected, 0.09 s, Lean error | 3.8 GB |
| KillTab (`tabOkB_S`, 10× `decide +kernel` over the table) | (part of 1,697 s) | 788 s with `TURBO_LEAN_TIMEOUT_MS`; fails after 30 s without it | | | | 2.2 GB |
| SpillInstCheckCompleteW (`spillInstOk_iRets`, `native_decide`) | | **rejected**: "Soundness hygiene violation … native_decide/ofReduceBool" | | | | |

The very first `check` on the machine also compiles the Zygote worker binary, which is then
cached in `/dev/shm/turbo-lean-staging-<uid>/fastcheck_shared_bins`. That first run took 30 s
with a 6.9 GB scope peak, once.

- **It accepts our files.** Custom tactics, `decide +kernel`, `set_option`s and the lakefile's
  `weakLeanArgs` linter options caused no problems (it gets the environment from `lake env`).
  Broken proofs were rejected each time, matching what lake would report: the same Lean error
  text, except for `handOk_try`, which hit the timeout instead.
- **Why it is fast:** every earlier theorem in the file becomes `:= sorry`, so a module's
  expensive `decide +kernel` theorems are skipped unless the edited theorem *is* one of them.
  Then the cost is that theorem's own kernel time (`tabOkB_S`: 788 s of KillTab's 1,697 s).
  Imports load once per warm worker (~1 s for KillTab); later edits only re-elaborate the
  edited theorem.
- **Default 30 s limit.** The worker's limit comes from `TURBO_LEAN_TIMEOUT_MS`, read by the
  daemon when it starts. `check --timeout` does not reach an already-running daemon. Heavy
  theorems need the variable set before the first `check` (or the daemon killed and restarted).
- **`native_decide` is rejected in every mode** (`server.rs`: source hygiene scan, no trusted
  exemption). Witness theorems that use it cannot be checked. Other theorems in the same
  witness file can be checked, but their prefix stubs it with `sorry`.
- **Daemons.** The first `check` starts `turbo-lean serve` plus `turbo_zygote` workers that stay
  running in the caller's memcap scope (1–4 GB each, 7 GB for the scope after a few checks).
  They outlive the command, and the scope stays alive with them. Kill them when done.
- **Not gate evidence:** the prefix is `sorry`'d, and cached verdicts are trusted. Merges keep
  `lake build` and the axiom audits.

### 2. Singleflight and memory governor (source reading)

- **Singleflight** (`db.rs` `acquire_singleflight`, used by `build` in `lake_build.rs` and per
  shard in `check.rs`): the key is a BLAKE3 hash over the whole project interface (or one
  shard). If `<cache>/locks/<key>.done` exists, its outputs are used. Otherwise the caller
  takes `flock(LOCK_EX|LOCK_NB)` on `<key>.lock`: the leader runs the work (plain
  `lake build <targets>` for `build`) and writes `.done`. Followers block on `LOCK_SH`,
  re-read `.done`, and take over as leader if it is missing (a crashed leader's lock is
  released by the kernel). This does not apply to plain `lake build`. The `build` key covers
  the whole project, not single modules. (Summary sent to BuildInfra for the cross-worktree
  lock in `scripts/lake-serial-build.py`.)
- **Memory governor** (`shm_cache.rs` `MemoryBudgetGovernor`, `zygote.rs`): the budget is
  `--max-memory-mb` or ¾ of MemAvailable. It only sets turbo-lean's own shard-worker count,
  the `/dev/shm` quota with disk spill, and an LRU that kills idle Zygote daemons above a
  machine-wide total (default 2–12 GB). `have`-block fission splits only theorems checked by
  `check` cold in low-memory mode (≤4096 MB) or with a cached cut. `--max-memory-mb 4096` did
  not change the times above. Nothing bounds a `lean` process run by `lake build`, so memcap
  stays our mechanism.

### 3. Statement pinning: `pr-verify --disallow-statement-changes`

Run on `origin/agent/build-diet` (`d8524602`) against `origin/main`:
- Without `--scope`, it fails before the statement check: "PR Hygiene & Axiom Gate FAILED …
  RegallocCheck.lean L140/L197/L243: csimp". It rejects `@[csimp]`, which build-diet adds on
  purpose.
- With `--scope FV/Backend/Proof` (4.8 s): it fails with 223 "statement-edited theorems" in 9
  files. That is every theorem in each touched file. IselCmpBase only gained an `import` line,
  yet all 35 of its theorems are flagged ("deleted"). The real changes (redefined
  `AState.remove/meet/le`, the deleted private `observed_1..7`) are lost in the noise.
  `--scope FV/E2E` still reports files outside the scope.
- It cannot replace our statement-hash dumps (kernel statement hashes per constant): it is
  file-granular and source-based, and it rejects `csimp`.

### Recommendation

- Agents MAY use `turbo-lean check --decl` to iterate on one theorem in a heavy module (usage:
  `docs/USAGE.md`; binary `~/.local/bin/turbo-lean`, built from
  `~/.local/share/turbo-lean/src` at `ded00b8`). Before the first call, set
  `TURBO_LEAN_TIMEOUT_MS`, `TURBO_LEAN_HOME` and `TURBO_LEAN_TELEMETRY=off`: telemetry to
  `telemetry.thomas.md`, an external host, is on by default. Run it under memcap, kill the
  daemons afterwards, and always finish with the normal lake build and audits before a PR.
- Do not use `build`, `pr-verify`, `ci-verify` or the governor. Keep the statement-hash dumps
  and `scripts/lake-serial-build.py`.

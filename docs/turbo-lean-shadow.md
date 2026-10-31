# Optional turbo-lean shadow experiment

This is a **non-blocking shadow experiment**, never a required check. Stock Lean remains
authoritative. The draft requests no merge. Before anyone relies on turbo-lean, collect
records for **20 consecutive main commits with zero unresolved correctness discrepancies**.
That record will be collected from workflow runs; this PR does not supply it or claim speedups.
Statement digests never authorize skipping stock kernel checks.

The job `turbo-lean-shadow` has `continue-on-error: true`. On main it follows the existing
Full gate build waves and assemble job, reads their verdict, and reuses their `lake-full`
artifact through `.github/actions/fv-lean`. It is not a dependency of any stock job or report.
The stock build, audits, compiler comparisons, ratchet and reporting retain their outcomes.

On PRs it follows the existing Stock compiler comparison job. That comparison measures
compiler output, so it is recorded as `prior_stock_job_result`, not mistaken for a Lean
proof verdict. The isolated shadow job restores the newest main `lake-full` with the same
`fv-lean` setup and runs a stock reference over `FV FVTest Corpus` and all root-package
executables, using the existing memory-aware scheduler. Lake checks input traces before
reusing outputs. With no baseline, the run stays incomplete rather than starting a cold
full build. A large PR may still exceed the time budget; that is a gap, not agreement.

turbo-lean is built from **80eaf322a67fdf6b370aeb95b592033e3c7ad358**, with the Cargo lockfile,
Rust 1.96.0, its own Lean 4.35.0 build toolchain and pinned LeanSys dependency. The executable
is cached by SHA, OS, architecture and toolchains; its source and build toolchain stay outside
the checked clifv tree. Verification uses clifv's cached Lean **4.34.1**, unchanged.
The invocations, from the repository root, are:

```sh
export TURBO_LEAN_TELEMETRY=off
export TURBO_LEAN_NO_REMOTE_TELEMETRY=1
export TURBO_LEAN_NO_WORKTREE_LINK=1
export LEAN_NUM_THREADS=4
turbo-lean --no-daemon --no-telemetry --no-auto-worktree-link \
  ci-verify --base "$BASE" --receipt ci-receipt.json
# PRs only:
turbo-lean --no-daemon --no-telemetry --no-auto-worktree-link \
  pr-verify --base "$BASE" --disallow-statement-changes --receipt pr-receipt.json
```

`BASE` is the PR's base SHA or `HEAD~1` on main. At the pinned revision the documented
worktree opt-out is the global `--no-auto-worktree-link`, not `--worktree opt-out`.
All local and remote turbo telemetry is disabled. Timings in the requested CI artifact are
explicit experiment results, not turbo telemetry. No persistent turbo daemon is used.
These commands use the default trusted mode under the same ordinary CI checkout model as
stock Lake, with read-only token permissions, no persisted Git credentials and no inherited
secrets. They are not an untrusted-code sandbox. There is no `pull_request_target` or
privileged `workflow_run` execution.

## Reading the artifacts

Download `turbo-lean-shadow-<sha>-<attempt>` from the parent workflow run. `result.json` contains:

| Field | Meaning |
| --- | --- |
| `commit`, `base`, `turbo_lean_sha` | Exact tested revision, baseline and verifier pin |
| `stock_ok` | Existing full-gate Lean build on main; isolated stock reference build on PRs |
| `turbo_ok` | `ci-verify` exit verdict |
| `discrepancy` | `stock_ok != turbo_ok`; `null` if either verdict is unknown |
| `wall_s.stock` | Main: first build-wave start to assemble completion, including scheduling; PR: stock reference build elapsed time |
| `wall_s.turbo` | CI verification elapsed time, excluding installation/cache restore and PR statement audit |
| `pr_ok`, `commands.pr` | Separate PR statement-policy verdict, command, exit status and duration |
| `commands`, `stock_source`, `prior_stock_job_result` | Provenance, exact commands and raw exit codes |

Logs, scheduler output and any receipts are in the same artifact. `true/false` are observed
exit verdicts, not a soundness proof; `null` means missing, setup failure or timeout. Inspect
the logs to classify a disagreement: turbo's hygiene/axiom policy is stricter than stock
compilation and its source discovery also sees nested Lean projects and audit scripts outside
the full-gate root targets. Statement edits deliberately fail `pr-verify`; `pr_ok` is kept
separate so this policy rejection is not mislabeled as a compiler-verdict discrepancy.
No allowlists, proof statements or source-discovery exclusions are added to hide differences.

For the 20-commit record, download and retain JSON plus logs, list main commits in first-parent
order, select a completed run for each exact SHA and verifier pin, and link any investigated
discrepancy to its resolution. Missing records, `null` verdicts and cancelled/dropped runs are
gaps: do not skip them to claim 20 consecutive commits. Full gate concurrency can drop pending
pushes; maintainers must rerun any missing exact revisions before counting a window. Artifacts
are retained 90 days; archive the accepted window before expiry. Neither check success nor
`discrepancy: false` alone establishes the 20-commit criterion. Timings have different scopes
and cache states and are not a paired performance benchmark.

## Disable or remove

Set repository Actions variable `TURBO_LEAN_SHADOW_DISABLED` to the string `true` to skip
both callers immediately. Alternatively remove only `shadow-experiment` from
`full-gate.yml` and `stock-compiler-comparison.yml`, then delete the reusable workflow and
helper. No branch protection or required checks should name this experiment; this change
does not edit those settings. The stock jobs do not depend on the experiment.

## Local validation before opening the draft

On 2026-10-31, with clifv at `08281d75094f7908cabf4bd79b71df76e09ff3d4`:

- actionlint 1.7.12 accepted all repository workflows. The Python script suite passed
  (88 tests, 7 skipped at the first run); the five shadow accounting tests also passed
  after the final timing-accounting test was added.
- Stock Lean 4.34.1 built `FV.Arm.MinTheory` and `FV.Arm.Attr` in the actual clifv checkout,
  with `LEAN_NUM_THREADS=4` and a 4 GiB memory cap.
- The pinned turbo-lean SHA built from source locally with Lean 4.35.0 and the available
  Rust 1.99.1. CI's pinned Rust 1.96.0 build was not executed locally.
- To keep the verifier dry run small, the two unmodified module sources were copied into
  a minimal Lake project using Lean 4.34.1. A second Git revision added only a comment.
  Stock Lake built that cone successfully. With telemetry off, `--no-daemon` and worktree
  opt-out, `pr-verify --base HEAD~1 --disallow-statement-changes` passed and emitted a receipt
  (two audited files, one theorem shard, zero statement edits).
- On that stock-built cone, `ci-verify --base HEAD~1` exited 1:
  `Worktree opt-out prevents compiling uncached module FV.Arm.Attr; build with Lake first`.
  A subsequent changed-statement probe also stopped at a stale-module/opt-out gate even
  after an explicit successful stock rebuild, so it did not establish statement-rejection
  parity. These are unresolved integration observations, not successful parity results.

The full clifv build, hosted workflow execution and 20-commit record were not run locally.
The initial CI/cache discrepancy is explicitly retained for investigation; no speedup is claimed.

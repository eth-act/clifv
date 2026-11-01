# Optional turbo-lean shadow experiment

This is a **non-blocking shadow experiment**, never a required check. Stock Lean remains
authoritative. The draft requests no merge. Before anyone relies on turbo-lean, collect
records for **20 consecutive main commits with zero unresolved correctness discrepancies**.
This draft does not supply that record or claim speedups. Statement digests never authorize
skipping stock kernel checks.

## Independent scheduling and trust

`turbo-lean-shadow.yml` is its own workflow, triggered by completion of **Full gate** on
`main`, or explicitly by `workflow_dispatch`. It has a separate `turbo-lean-shadow-*`
concurrency group and a `continue-on-error: true` job. `full-gate.yml` and
`stock-compiler-comparison.yml` are identical to upstream: neither calls nor waits for shadow.
The experiment cannot hold Full gate's concurrency slot or delay the fork-PR stock-comparison
publisher's workflow-completion trigger. It still consumes a runner when eligible.

The workflow has only `contents: read` and `actions: read`, no inherited secrets, and no
persisted checkout credentials. Automatic `workflow_run` execution checks out the controller
at the trusted default-branch `github.sha`. Before checking out any measured code, it validates
the triggering run through the API: the run must be a completed same-repository Full gate run,
from `push`, `schedule` or `workflow_dispatch`; automatic runs must also match the triggering
main SHA and attempt. It never checks out or executes a fork PR head with an elevated token.
Only the validated stock revision is checked out under `source/`. The controller remains in
the separate original checkout. These commands use turbo's default trusted mode and are not
an untrusted-code sandbox.

The main verification path requires a successful provenance step, a successful original
Full gate run, successful Plan job and successful stock build. Failed-stock runs retain the
real failure in their record but skip the expensive setup and verifier. Missing API data,
cancelled/skipped builds, absent artifacts and setup failures remain incomplete. The job is
capped at **75 minutes**, the source build at **25 minutes**, and each verifier invocation at
**15 minutes**, with `timeout --foreground` so memcap can own the command's process group.

There is **no automatic PR trigger**, including for fork PRs, to avoid long shadow/reference
build costs. For an opt-in same-repository PR experiment, a maintainer can first dispatch
Full gate on that branch, then dispatch this workflow with its completed `stock-run-id` and
optional full `base-sha`. The latter enables the separate `pr-verify` statement-policy audit.
Run the controller from a trusted workflow revision; only read-only tokens are granted.
Fork PR heads are not accepted as a stock source; a maintainer would first need to bring the
reviewed revision onto a same-repository branch. No stock reference is rebuilt by shadow.
Manual branch experiments do not count toward the main-commit record.

While this remains a draft, automatic `workflow_run` activation requires the workflow to
exist on the default branch. No merge or hosted experiment activation is requested here.

## Cache isolation and binary provenance

Shadow does **not** call `.github/actions/fv-lean`, whose post-step saves shared stock keys.
The stock Lean toolchain uses `actions/cache/restore` only. On a miss the pinned archive is
installed without saving a stock cache key. The `lake-full` artifact is downloaded from the
validated original run into an isolated runner-temporary Lake cache. No shared stock Lake or
compiler cache is saved. All writable Actions cache keys start with `turbo-shadow-`.

The executable is built from the **personal repository**
[Th0rgal/turbo-lean](https://github.com/Th0rgal/turbo-lean), pinned to
**0212d865be1a1093decef308225a0badcdccb526**; it is not an official Lean binary. The workflow
checks the fetched commit SHA and uses its Cargo lockfile, Rust 1.96.0, its own Lean 4.35.0
build toolchain and pinned LeanSys dependency. Downloads of both Lean archives are checked
against pinned SHA-256 sums. The executable cache includes SHA, OS, architecture and
toolchains; source/build tools stay outside the checked clifv tree. Verification uses clifv's
Lean **4.34.1** with four Lean threads and a 12 GiB memcap.

The invocations from the validated source root are:

```sh
export TURBO_LEAN_TELEMETRY=off
export TURBO_LEAN_NO_REMOTE_TELEMETRY=1
export TURBO_LEAN_NO_WORKTREE_LINK=1
export LEAN_NUM_THREADS=4
turbo-lean --no-daemon --no-telemetry --no-auto-worktree-link \
  ci-verify --base "$BASE" --receipt ci-receipt.json
# Opt-in manual PR audit only:
turbo-lean --no-daemon --no-telemetry --no-auto-worktree-link \
  pr-verify --base "$BASE" --disallow-statement-changes --receipt pr-receipt.json
```

`BASE` is the supplied full PR base SHA or the tested commit's `HEAD~1`. At the pinned revision
the documented worktree opt-out is the global `--no-auto-worktree-link`. All local and remote
turbo telemetry is disabled in the workflow and command environment. Artifact measurements
are explicit experiment results, not turbo telemetry. No persistent turbo daemon is used.

## Reading the artifacts

Download `turbo-lean-shadow-<sha>-<attempt>` from the **independent shadow workflow run**.
Before eligibility is established, the artifact name uses the shadow run ID in place of SHA.
`result.json` schema 2 contains:

| Field | Meaning |
| --- | --- |
| `commit`, `base`, `turbo_lean_sha` | Exact tested revision, baseline and verifier pin |
| `stock_ok` | Real original Full gate build-wave/assemble job result, obtained via the API; never a shadow rebuild |
| `stock_source` | Original run and attempt provenance; initialized to `null` |
| `stock_run_id`, `stock_run_attempt`, `stock_run_conclusion`, `stock_branch`, `stock_run_event`, `stock_jobs` | Original run identity and raw Plan/build job conclusions with timestamps |
| `eligible` | Original run, Plan and stock all succeeded; permits expensive shadow steps |
| `turbo_ok` | `ci-verify` exit verdict |
| `discrepancy` | `stock_ok != turbo_ok`; `null` if either verdict is unknown |
| `wall_s.stock` | First original build-wave start to assemble completion, including scheduling; excludes unrelated jobs |
| `wall_s.turbo` | CI verification time, excluding installation/cache restore and PR audit |
| `pr_ok`, `commands.pr` | Separate manual PR statement-policy verdict, command, exit status and duration |
| `commands`, `stock_lookup_error` | Exact verifier commands/raw exit codes, or incomplete provenance error |
| `event`, `run_id`, `run_attempt` | Independent shadow run identity, distinct from the stock source |

`stock_ok: true` requires successful assembly and only successful/skipped build-wave jobs;
a failed build job yields `false`. Missing/cancelled/skipped assembly without a build failure
is `null`. A later rerun cannot replace the attempt that triggered an automatic record.
There is no shadow reference build. If one is added later, its verdict must use a separate
field such as `shadow_reference_stock_ok` and must never populate `stock_ok`.

Logs and any receipts are in the same artifact. `true/false` are observed exit verdicts,
not a soundness proof; `null` means missing, setup failure or timeout. Inspect disagreements:
turbo's hygiene/axiom policy is stricter than stock compilation and its source discovery also
sees nested Lean projects and audit scripts outside the full-gate root targets. Statement
edits deliberately fail `pr-verify`; `pr_ok` is separate from compiler-verdict discrepancy.
No allowlists, proof statements or source-discovery exclusions hide differences.

For the 20-commit record, retain JSON plus logs, list main commits in first-parent order,
and select a completed successful run for each exact main SHA and verifier pin. Require
`stock_branch: main`, the expected first-parent base, `stock_ok: true`, `turbo_ok: true`,
a successful original run and Plan, and resolve and link any investigated discrepancy.
**Failed-stock runs are not counted toward the 20-commit agreement record**, even if a
future verifier also fails. Such a commit breaks the window until successfully rerun;
do not skip it. Missing records, `null` verdicts and cancelled/dropped runs are also gaps.
Full gate and shadow each have their own concurrency queues, which can drop pending runs;
maintainers must rerun missing exact revisions. Use manual dispatch with the exact stock run
ID for a missing shadow record. Artifacts are retained 90 days; archive the accepted window
before expiry. Check success or `discrepancy: false` alone does not establish the criterion.
Timings have different scopes/cache states and are not a paired performance benchmark.

## Disable or remove

Set repository Actions variable `TURBO_LEAN_SHADOW_DISABLED` to string `true` to skip the
independent job. Alternatively disable/delete only `turbo-lean-shadow.yml` and its helper.
No stock-workflow edits are needed. No branch protection or required checks should name this
experiment; this change does not edit those settings.

## Quorum r1 revision validation

- actionlint 1.7.12 validates all repository workflows.
- `python3 scripts/test_turbo_lean_shadow.py` covers real command exits/timeouts, telemetry,
  original-attempt provenance, API pagination, rejected fork/PR sources, failed or missing
  stock jobs, failed Plan/run gating and separate PR policy accounting.
- A read-only API smoke check uses an actual completed Full gate run. It does not execute
  the hosted shadow job, a full clifv build or the 20-commit experiment.

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

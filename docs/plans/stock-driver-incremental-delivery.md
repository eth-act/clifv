# Incremental Stock driver delivery

Current execution plan, refreshed 2026-10-18; replaces the wholesale-cutover ordering in
[test-binary-alignment-recovery.md](test-binary-alignment-recovery.md). Historical
proof checkpoints remain evidence, not a queue of instructions to resume.

## Decision and current baseline

Land dependency-closed work on main continuously. Introduce Stock into production
one proved class of **complete functions** at a time, with legacy fallback for
all other inputs. Do not wait for every Stock rule family, effect and exception
case before shipping the first proved production class.

#246 (`fc4a06f3`) and #247 (`5a3ad2bb`) are merged. Their preparation/CFG foundations
are available now. The roadmap itself landed in #263 (`0ec908f6`).
Inspected main: `73784c9c2d8625169f3e6d2a16e378ae0aeaca29` (2026-10-18). Production `Backend.lowerChecked`
still calls `lowerFunction` and `Proof.Driver.lowerCheck`. The experimental
`FVTest/Backend/Lowering/StockComparison.lean` runs Stock and marks its output
unverified; scan replay alone does not prove original-source correctness.

The original full #140 goal remains: all original in-scope functions, source and
machine semantics, simulation and completeness, compiler/checker/linker/generated
proof consumers, original theorem variants and required axiom sets. Staging changes
implementation order, not the accepted input domain or final obligation.

## Reconciliation baseline: what changed since #263

Main gained 32 commits after the roadmap merge (33 from its inspected `8a3284bf`
base), touching 71 Stock paths. These are source overlaps, not an asserted merge
conflict count. Published Stock ports are already on main; private kernels from
the saved old tree have not been reconciled or revalidated against them.

| Landed change | Consequence for our next landing |
| --- | --- |
| #264: f32/f64, Inst.float and type/class distinctions | Keep main's published Stock ports. Audit the explicit `isInt` and trailing auto-parameter changes, especially high-multiply and select roots. A concrete integer caller still elaborating does not prove the old universally quantified theorem statement was retained. Derive integer-ness from real source invariants or retain an explicit integer-domain compatibility variant; width alone is insufficient. Record old/new propositions and axioms instead of silently accepting strengthened premises. |
| #277/#278: FP ABI/data movement; Stock float rejection; expanded rule closure | Reuse `StockFloatCheckDomain.buildCtx_int_domain` / `buildCtx_functionE_domain` as the existing integer-domain preservation argument, checking their hypotheses at each use. Stock still rejects noninteger value contexts; the global compiler must continue accepting main's typed inputs through the current legacy route. Update pinned constructor/coverage counts from actual source, not saved integer-only counts (the published partition is now 155/362). |
| #284/#290/#296: typed context, driver, shape and checker proofs | Reconcile saved imports and proof assumptions with `Compile.functionET`, `LowerShapeT`, `lowerFunction_runT` and `lowerCheckT_complete`. Reuse their integer compatibility facts where applicable. These are proofs of the layout-order driver, not a certificate for Stock; do not redirect Stock through `lowerCheckT` without its own soundness bridge. |
| #287/#289/#295/#298: Lean allocator, now the CLI default, plus completeness proofs | Preserve the current Lean allocation route and `FV_RA_OUT` answers consumed by cargo-fv/link proofs. Stock comparison/numbering and trace tests deliberately select regalloc2; keep that settings-matched oracle path. Derive any Lean allocator completeness hypotheses for Stock's actual prepared code; raw EdgeVCode is not automatically in its domain. |
| #282/#288/#291/#293/#297: Lean linker and executable-totality integration | Base consumer adapters on current linker/layout/relocation contracts, including the existing `--lean-ld` route where affected. Do not resurrect old generated-proof or linker assumptions, or fold an unrelated linker replacement into the first Stock activation. |
| #306/#307/#309/#312: atomics/concurrency specifications and contracts | Record the changed Arm/CLIF/world dependencies when porting effectful packets. The first pure D0 class does not depend on proving the Stock atomic path; do not block its adapter on the later effect/concurrency migration. |
| #265/#266: author squash merges and post-merge full validation | Authors land after per-PR gates; neither CI completion nor the continuous full gate is a pre-merge prerequisite. Tell the integrator the actual merge commit. Docs-only PRs have no required runtime/build/CI wait. |

At inspection, #261 reports last green `a386cbab`, one commit behind `73784c9c`.
This is recorded evidence, not a claim that the inspected tip is fully green.
Fetch main and re-read #261 before each actual implementation landing; refresh
only the affected packet and adapters rather than restarting a global port.

## The safe migration boundary

For an input-only decidable predicate `D`, prove the actual Stock path correct for
arbitrary functions and values in `D`. The dispatcher tries that path only in `D`.
Every other input uses legacy. Any Stock-path compilation failure retries legacy
with the same input/settings, before publishing any artifact. The fallback covers
preparation, allocation/checking, physical lowering and emission failures, not just
`Stock.lower` errors. It must preserve the existing successful legacy stages and
acceptance, including both cleanup modes and the original #179 identities.

`D` is an internal rollout decision, never a new caller premise or an admission
filter for the compiler. No name/fixture allowlist, output equality test, scan
replay result or corpus pass can substitute for the proof. Stock success requires
source-to-machine correctness for the emitted artifact; legacy retry establishes
combined acceptance/totality from the existing legacy guarantee when Stock fails.
Stock-only totality/completeness remains a separate full-goal obligation.

The minimum default-enabled unit is one complete function path through all affected
consumers. Do not mix individual legacy/Stock instructions until shared demand,
alias, deferred-effect and scheduling invariants justify that composition. Do not
run legacy `lowerCheck` on a Stock result and assume its old soundness theorem
applies: it is tied to legacy construction. Do not discard per-successor `edgeArgs`
when adapting Stock to an interface that takes `VCode`.

## Ordered landings

Each row is a semantic unit or a short stack of such units, not one final mega-PR.
Keep at most one active implementation batch and one dependent review batch. A
finished unit is squash-merged by its author after per-PR gates, before unrelated
proof expansion continues; notify the integrator of the resulting commit.

| Order | Landable unit | Required result and limit |
| --- | --- | --- |
| 1 | Compatibility and proof backlog | Reconcile with current main and Kev's listed type changes. Publish the smallest existing dependency-closed proof packet, starting with retained records/result binding/alias framing, then forms/classes/outgoing facts and source-call/body facts as their dependencies permit. Each packet retains its real source witness, audits and exact inherited axioms. Do not wait to integrate all scratch modules together. These landings reduce divergence; they do not claim production cutover. |
| 2 | Common pipeline seam, legacy instance | Factor a minimal lowering/preparation boundary used by the real compiler and proof consumers. Preserve the current-main legacy result definitionally or prove an exact compatibility lemma; keep the Lean allocator default and allocation-answer provenance. Represent legacy `VCode` and Stock's edge-aware result explicitly, joining only at a genuinely common prepared/allocation boundary. Keep old entry points/theorems as wrappers; prove unchanged legacy acceptance, errors and artifacts. Do not generalize unrelated compiler layers. |
| 3 | Additive consumer adapters | Factor the specific legacy-bound facts used by E2E, scope/totality, layout/relocation/linking and generated-proof emission. Instantiate every new interface with legacy first. Migrate consumers in separate additive PRs with compatibility lemmas, while production remains legacy. Runtime objects contain data; compile-correctness obligations are fixed Lean theorems, not new per-program certificates. |
| 4 | Stock path behind explicit experimental selection | Wire the existing edge-aware preparation/allocation/checking route into the common compiler seam, retaining rules, settings, relocation, unwind/LSDA and diagnostic metadata. Exercise real tools and artifacts. Keep experimental output explicitly unverified until its source-to-machine and consumer proofs exist. Never satisfy `--verified` by relabelling replay-checked output. This wiring can land before full Stock semantics. |
| 5 | First complete proved production class `D0` | Start with one-block integer functions that return their sole ordinary entry parameter, initially i32/i64, with no body statements, effects, calls or exceptional terminators. Define the predicate from input syntax/ABI and prove its entire actual Stock entry-to-return path for all parameter values, including dirty upper bits. Derive allocation/checker/physical/emission and consumer obligations internally. Add inhabited universal-value witnesses and a mixed legacy/Stock program witness. This is a proposed first class; narrow its implementation complexity or choose an equally simple class only with a written reason, never by fixture identity. |
| 6 | Enable `D0` by default | Only after the real compiler, checker, linker and generated-proof consumers cover the same selected artifacts, enable input dispatch plus transactional legacy fallback. Add the combined correctness/acceptance theorem without changing original public input conditions. Test Stock success, forced allocator/fallback paths, a forced Stock-path failure reaching legacy, and mixed-program linking/verified proof generation. A passing internal Stock fixture is insufficient. This is the first production Stock milestone. |
| 7 | Grow production classes | Extend the selector monotonically after each complete proof: straight-line pure integer operations; multi-block branches/parameters/loops; memory/traps; ordinary direct/indirect/GOT calls and sret; TryCall/exception continuations. Reorder independent classes to match completed evidence. For every extension, prove the new complete function path and preserve previously enabled classes; any still-unsupported combination falls back to legacy. Land family proofs as they finish, without waiting to enable their class. |
| 8 | Complete replacement and retire compatibility | Cover every original input/family/effect and prove Stock-only simulation AND completeness/totality. Remove the rollout fallback only with that argument, preserving current-main accepted inputs as well as the original baseline. Retire old implementation consumers separately after compatibility users migrate; retain old theorem variants as required. Run the final fresh complete settings-matched comparison and all original acceptance/stage/trust checks. Only then close #140. |

Rows 2 and 3 may interleave as small adapter PRs; row 1 continues only when needed
for the next production class. Do not postpone the seam and `D0` work until all
call/TryCall scratch proofs are finished. Before another new family lemma, state
which numbered landing it unblocks and why already saved work cannot supply it.

## First execution batch and divergence control

The next task is a small code/proof reconciliation landing, not another global
inventory or wholesale rewrite. This refresh does not claim that landing is done.

1. Compare the canonical saved tree and latest verified recovery snapshot
   (`agent/stock-driver-wip-backup-20261018T032106Z`, `c40421d4`) with current main.
   Preserve all unpublished sources/evidence. Start with the already-landed return
   path (`StockReturnDriverRuns` / `StockReturnSourceWitness`) and the saved
   `StockReturnStatic*` / `StockReturnPlacedStatic` packet as a concrete D0-related
   candidate. Check which modules are absent, their import closure and actual
   witnesses; do not assume these candidate names define a closed or validated
   packet. Drop already-landed deltas and select the smallest necessary closure.
   If its closure pulls in unrelated call/TryCall work, defer that packet and land
   the minimal legacy-preserving pipeline seam instead. The backlog is not a gate
   ahead of that seam. Time-box this selection to the first working session.
2. Produce one packet manifest with paths, current-main base/import hashes,
   original/current theorem propositions and exact axiom sets, complete witnesses,
   affected interfaces, passed/missing checks and next dependent landing. Port only
   that closure onto main's published float changes; do not overwrite main with the
   old canonical tree or claim old-head kernels are current evidence. Open its
   non-draft PR after per-PR checks and squash-merge promptly under §7.
3. Coordinate the concrete overlap in #140 before implementation: Kev's floats
   and register-allocation agents have already posted their ports. His #52 status
   also lists **StockSeam** for reducing Stock rebuild fan-out. That import/build
   seam is distinct from our runtime lowering/preparation contract, but may touch
   the same files. Ask for its branch/file/interface boundary, reuse it when it
   lands, and pause only actual overlapping edits. Keep his FP/ABI/shared-model
   work moving; do not create a global freeze or duplicate its port.
4. Next land the minimal common pipeline boundary instantiated with current-main
   legacy lowering, allocation defaults and answer receipts, with exact legacy
   compatibility. Post a concrete proposed signature and consumers in #140 before
   shared production edits. Use D0's entry-parameter return as the first vertical
   proof target; no new constant/call/TryCall family is a prerequisite. Prepare
   additive consumers against the typed-driver and current linker APIs.
5. Reconcile each small PR with a newly fetched main tip before squashing. Re-run
   affected checks for a nontrivial rebase, report actual overlap/failure and retain
   successful source-matching evidence. Keep one active implementation batch and
   at most one dependent review batch; no long frozen tree plus growing private
   proof backlog. The old stopped canonical build queue is retired, not resumable
   proof of current-main validation.

## Validation, integration and evidence

Use **current main's adopted policy** in docs/TO-PROVE.md §7: #260, updated by
#265 (`84dc739d`), the checked-in #262 axiom audit and post-merge #266 full CI.
This supersedes both the old full-per-PR backlog rules and #263's integrator-only
merge/CI-wait instructions. Authors squash-merge after their per-PR gates, without
waiting for GitHub CI or a full-main run, then tell the integrator the PR/commit.
The integrator owns continuous full validation on #261 and failure triage.

- Documentation-only PRs: no required gates under §7 (still check the actual diff
  and links). Implementation PRs: affected builds and per-PR
  runtime gates, new/changed theorem axioms, and the E2E audit when dependencies
  change, as specified by §7. Use the shared scheduler/cache and its ≤16 GiB author
  budget; request the integrator's heavy lane for a genuinely heavier required
  kernel instead of launching another full build or weakening a theorem.
- Lowering/preparation/encoding/allocation changes exercise runtime and encoding;
  E2E/link/scope changes exercise E2E and link-check; driver/cargo changes exercise
  verified fv-demo and survey. Keep both original 1,150-identity cleanup-mode
  reports and exact stage parity as an additional Stock regression requirement.
- At production-class activation, add the end-to-end tests and complete witnesses
  in rows 5–7, exact artifact/proof provenance and settings-matched comparison for
  the changed class. Request an immediate continuous full-main run after activation
  or broad shared-interface changes. Record the exact tested commit and last green
  #261 commit; do not represent a previous head's success as current evidence.
- No sorry/admit/new handwritten axioms, silent premise strengthening, omitted
  effect checks or passing corpus substituted for universal proofs. Preserve old
  variants and exact required axiom sets. Use cached source-matching observations
  and one bundled MCP review per coherent theorem packet; no consecutive redundant
  per-theorem verification loops. Full public/private/generated-constant scans
  remain part of the packet's trust evidence.
- Record per-PR gate lines in the non-draft PR body, fetch/reconcile current main
  and squash-merge immediately after those gates pass; no CI/merge-ready-label/
  integrator-queue wait. Notify the integrator of the PR and actual merge commit.
  Monitor post-merge CI/main-gate results and prioritize a fix or revert if red.
  Track actual squash commits rather than PR/module counts as production progress. Roughly eight substantive
  PRs/day is a pacing target, not permission to fragment a semantic unit or bypass
  a gate. If blocked, publish the exact failing dependency and next action in #44.
- Update #44 after commits, scope changes and stops, and #140 for shared boundaries
  and landed milestones. Keep source/evidence remotely backed up independently of
  readiness. Remove unneeded clean worktrees/caches at each batch, preserve dirty
  work and unique ignored evidence, retain one warm cache, and keep the shared
  resource budget from AGENTS.md. No worktree/build is needed for this plan edit.

## Completion accounting

Track separately: proof packets merged; common consumer adapters merged; experimental
Stock available; proved production classes enabled; original-domain coverage still
using legacy; Stock-only completeness; final fallback retirement. A production
class counts only when the actual shipped route and its checked proof consumers
agree. Adapter or proof landings alone do not count as driver activation.

Incremental replacement is possible. What cannot safely be separated is enabling
a Stock-produced function while its source-to-machine argument or any consumer
still reasons about legacy output. That coupling sets the size of each activation
PR; it does not require a single all-families, all-programs wholesale swap.

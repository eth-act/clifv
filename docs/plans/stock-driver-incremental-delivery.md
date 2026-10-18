# Incremental Stock driver delivery

Current execution plan, 2026-10-17; replaces the wholesale-cutover ordering in
[test-binary-alignment-recovery.md](test-binary-alignment-recovery.md). Historical
proof checkpoints remain evidence, not a queue of instructions to resume.

## Decision and current baseline

Land dependency-closed work on main continuously. Introduce Stock into production
one proved class of **complete functions** at a time, with legacy fallback for
all other inputs. Do not wait for every Stock rule family, effect and exception
case before shipping the first proved production class.

#246 (`fc4a06f3`) and #247 (`5a3ad2bb`) are merged. Their preparation/CFG foundations
are available now. Inspected main: `8a3284bf`. Production `Backend.lowerChecked`
still calls `lowerFunction` and `Proof.Driver.lowerCheck`. The experimental
`FVTest/Backend/Lowering/StockComparison.lean` runs Stock and marks its output
unverified; scan replay alone does not prove original-source correctness.

The original full #140 goal remains: all original in-scope functions, source and
machine semantics, simulation and completeness, compiler/checker/linker/generated
proof consumers, original theorem variants and required axiom sets. Staging changes
implementation order, not the accepted input domain or final obligation.

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
finished unit goes to the integrator before unrelated proof expansion continues.

| Order | Landable unit | Required result and limit |
| --- | --- | --- |
| 1 | Compatibility and proof backlog | Reconcile with current main and Kev's listed type changes. Publish the smallest existing dependency-closed proof packet, starting with retained records/result binding/alias framing, then forms/classes/outgoing facts and source-call/body facts as their dependencies permit. Each packet retains its real source witness, audits and exact inherited axioms. Do not wait to integrate all scratch modules together. These landings reduce divergence; they do not claim production cutover. |
| 2 | Common pipeline seam, legacy instance | Factor a minimal lowering/preparation boundary used by the real compiler and proof consumers. Preserve the actual legacy result definitionally or prove an exact compatibility lemma. Represent legacy `VCode` and Stock's edge-aware result explicitly, joining only at a genuinely common prepared/allocation boundary. Keep old entry points/theorems as wrappers; prove unchanged legacy acceptance, errors and artifacts. Do not generalize unrelated compiler layers. |
| 3 | Additive consumer adapters | Factor the specific legacy-bound facts used by E2E, scope/totality, layout/relocation/linking and generated-proof emission. Instantiate every new interface with legacy first. Migrate consumers in separate additive PRs with compatibility lemmas, while production remains legacy. Runtime objects contain data; compile-correctness obligations are fixed Lean theorems, not new per-program certificates. |
| 4 | Stock path behind explicit experimental selection | Wire the existing edge-aware preparation/allocation/checking route into the common compiler seam, retaining rules, settings, relocation, unwind/LSDA and diagnostic metadata. Exercise real tools and artifacts. Keep experimental output explicitly unverified until its source-to-machine and consumer proofs exist. Never satisfy `--verified` by relabelling replay-checked output. This wiring can land before full Stock semantics. |
| 5 | First complete proved production class `D0` | Start with one-block integer functions that return their sole ordinary entry parameter, initially i32/i64, with no body statements, effects, calls or exceptional terminators. Define the predicate from input syntax/ABI and prove its entire actual Stock entry-to-return path for all parameter values, including dirty upper bits. Derive allocation/checker/physical/emission and consumer obligations internally. Add inhabited universal-value witnesses and a mixed legacy/Stock program witness. This is a proposed first class; narrow its implementation complexity or choose an equally simple class only with a written reason, never by fixture identity. |
| 6 | Enable `D0` by default | Only after the real compiler, checker, linker and generated-proof consumers cover the same selected artifacts, enable input dispatch plus transactional legacy fallback. Add the combined correctness/acceptance theorem without changing original public input conditions. Test Stock success, forced allocator/fallback paths, a forced Stock-path failure reaching legacy, and mixed-program linking/verified proof generation. A passing internal Stock fixture is insufficient. This is the first production Stock milestone. |
| 7 | Grow production classes | Extend the selector monotonically after each complete proof: straight-line pure integer operations; multi-block branches/parameters/loops; memory/traps; ordinary direct/indirect/GOT calls and sret; TryCall/exception continuations. Reorder independent classes to match completed evidence. For every extension, prove the new complete function path and preserve previously enabled classes; any still-unsupported combination falls back to legacy. Land family proofs as they finish, without waiting to enable their class. |
| 8 | Complete replacement and retire compatibility | Cover every original input/family/effect and prove Stock-only simulation AND completeness/totality. Remove the rollout fallback only with that argument. Retire old implementation consumers separately after compatibility users migrate; retain old theorem variants as required. Run the final fresh complete settings-matched comparison and all original acceptance/stage/trust checks. Only then close #140. |

Rows 2 and 3 may interleave as small adapter PRs; row 1 continues only when needed
for the next production class. Do not postpone the seam and `D0` work until all
call/TryCall scratch proofs are finished. Before another new family lemma, state
which numbered landing it unblocks and why already saved work cannot supply it.

## First execution batch and divergence control

1. Inventory saved source against current main and the last remote recovery snapshot
   (`agent/stock-driver-wip-backup-20261017T143950Z`, `65aa544b`). Preserve every
   dirty/unpublished source and evidence file. Build a packet manifest: paths,
   import closure, original/current statement and axiom hashes, complete witnesses,
   shared interfaces, missing checks, branch/PR and next dependent landing.
2. Review Kev's floats-types rebase against #246/#247. He owns Clif.Ty/CTy.ofClif,
   FP register/ABI changes, shared Arm/ExtSem/exception interfaces and their port.
   We own Stock retained-record/source composition and the new migration seam.
   `StockReturnSourceWitness` and any changes to Stock.buildCtx/instArgs/mustLower
   require an explicit boundary in #140 before overlapping implementation. Do not
   hold his unrelated merges while finishing our whole-driver proofs.
3. Push the first closed proof packet and open a non-draft PR after its per-PR
   gates; start the minimal legacy-preserving seam next. Record actual dependencies
   and incomplete results instead of claiming all saved scratch kernels are ready.
   Once the seam has a concrete draft interface, post it in #140 before changing
   shared production consumers. Do not invent an interface freeze for Kev here.
4. Reconcile each small PR with current main before integration. Resolve only the
   affected overlap and rerun affected checks. Keep the unpublished dependent stack
   shallow; do not freeze the whole canonical checkout for a long gate run while
   continuing to accumulate another private implementation.

## Validation, integration and evidence

Use **current main's adopted policy** in docs/TO-PROVE.md §7, merged in #260
(`074a69cc`), plus the checked-in axiom audit from #262. This supersedes historical
instructions here that called #258's policy only a proposal or required every
full gate before each PR. The integrator owns merges and the continuous full main
gate on #261. Authors do not merge their own PRs. All merges are squash merges.

- Documentation-only PRs: CI. Implementation PRs: affected builds and per-PR
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
- Label a genuinely ready PR `merge-ready`, record per-PR gate lines in its body,
  and hand it to the integrator promptly. Track actual squash commits rather than
  PR counts or module counts as production progress. Roughly eight substantive
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

# Incremental Stock driver completion

Execution plan updated 2026-10-21 after the user's efficiency review. Supersedes
the historical ordering/checkpoints in this file and the recovery roadmap;
saved source and historical receipts remain preserved. Full original #140 scope
is unchanged: actual Stock source semantics, simulation/completeness, production
compiler/checker/linker/generated proofs, original inputs/theorem variants/exact
required axioms/accepted identities/successful stages.

## Active refresh: 2026-10-29 (supersedes earlier next-step ordering)

Baseline: main `c533c22a` (#755). The preserved October27 memory implementation
is `3753d98a` (verified on its old base) / `52b22dc9` (interrupted new-base
validation). Neither old receipt certifies current main. Saved source, branches
and remote evidence remain; recovery uses durable `.git/agent-evidence/` storage
rather than relying on `/tmp` surviving a restart.

The goal remains aligned. Main still has no `StockMemory` source domain or
paired initialized-load/return consumer. Reuse the saved memory proofs; do not
reimplement Kev's landed allocator, frame, checker or typed-linking machinery.

| Work | Current owner/state | Our boundary |
| --- | --- | --- |
| regalloc2 / Cranelift input numbering | Kev, landed | Reuse `CraneliftInput`; no second numbering adapter |
| AArch64 frame / unwind / frame-aware QA | Kev, #743 landed | Adapt internal memory consumers to the new frame; preserve original public source contracts |
| typed Stock linking / route placement / fast checks | Kev, #747/#748/#755 and earlier landed | Keep typed dispatch, exclusions, scope shortcuts and existing providers |
| branch order / MachBuffer | Kev, #553 active | No competing branch-layout implementation; coordinate any shared Stock/code metadata changes |
| scheduler / CI / proof speed | Parithosh, landed fixes and open #757 | Reuse results and CI cache; no independent proof-performance project |
| Lean module system | Parithosh, #726 prototype | Do not merge or duplicate its broad header port; coordinate leaf imports/generators |
| original-source initialized memory under Stock | Our saved packet, not landed | Complete the unique missing proofs and minimal additive production route |

### Immediate delivery sequence

1. Port the preserved memory packet onto current main. Keep the new compiler's
   `pipelineT`/`allocNone`, CraneliftInput, typed linker, placement shortcuts,
   frame-aware consumers and dead-cleanup generator. Resolve source overlap
   explicitly in #140; no blind replacement with old adapters.
2. Build the affected memory proof/consumer closure first, with the sole shared
   artifact cache and published CI artifacts where compatible. This is an early
   diagnostic pass, not a waiver of author gates. Fix actual port errors before
   launching the full author queue. Keep one validation head fixed during each
   healthy batch. Do not replay a completed healthy cohort without changed inputs
   or an unresolved concern.
3. Run current per-PR gates from TO-PROVE §§7–8: FV/FVTest/affected tools,
   transitive axiom audit, relevant runtests/encoding, E2E identity and successful
   stage parity, actual verified linking/examples and crate proofs. Include a
   complete actual initialized-load PC0 paired witness, default compiler/checker/
   linker/generated-proof consumers, both cleanup modes, actual default regalloc2
   and retained Lean allocator execution, and full prior-pipeline retry.
   Recover old evidence with its actual source hashes; never relabel it current.
4. Push backups, publish and squash a substantive memory delivery after current
   gates; notify the integrator. Remove completed expendable outputs only after
   unique evidence is archived and verified. Do not wait for unrelated full-main
   CI to grant author approval, and do not represent a targeted build as a full
   build or an optional route as completeness.
5. Use the captured two-block/nop memory function as the next concrete target.
   Generalize the existing retained-load body and guarded/paired omission proofs,
   then reuse existing CFG entry/edge/return composition. Keep old variants.
   Measure eligibility, selected actual Stock route and output/relocation parity
   on the same captured source cohort. Synthetic positive witnesses alone do
   not establish useful real-function coverage or an agreement gain.
6. Continue the unchanged original goal: broader addressing and memory effects,
   atomics, calls/exceptions, remaining scalar/rule families, nonempty conditional
   successor arguments, tables/loops, whole-driver source/block simulation and
   original-domain Stock-only/downstream completeness. Existing fallback preserves
   acceptance; it does not discharge any of these obligations.

### Batch evidence and resources

Before and after each batch, update #44 with source/base hashes, exact passing
and failing receipts, modules, next step, worktree/cache ownership and UTC time.
All merges are squash merges under the user's standing push/merge authorization.
Keep the four preserved source views and one shared warm artifact cache; no new
worktree or agent is needed for this refresh. Build budget <=16GiB, <=2 jobs,
<=4 CPUs, OMP_NUM_THREADS=2 and OMP_THREAD_LIMIT=2; use low priority. Free-space
target >=100GiB, hard floor >=50GiB after projected growth. CI download/staging
is temporary and removed after verified cache import. Preserve every unpublished
source/branch and all unique validation evidence.

The interrupted October27 new-base build is not counted passed. As of refresh,
its service is inactive, no compiler jobs are running, and temporary receipts are
gone. Verified3753 receipts and next-source drafts are preserved on the append-only
remote evidence branch; those remain historical evidence, not current validation.

## Current delivery: forward CFGs and conditional scalar leaves

PR #633 (`ac302a8a`) activated three-block chains. PR #634
(`d6218f29`, merged2026-10-26T22:23:16Z) removes that fixed bound and the older
two-block forwarding restriction.
[Terminal author evidence](../research/stock-forward-cfg-production.md) records
4,093 normal keys, 94 audit files/3,592 roots/all 3,544 old axiom sets exact,
78 new and 78/70/34/34 retained integration checks, 24,000 native executions,
and runtime/encoder/identity/stage/example/actual-crate/paired-output gates.
All 2,474 prior backend proof files and three shared theorem headers are exact.

Default compiler/checker/verified-linker/generated consumers append route 8 and
retain complete previous-route fallback on original inputs/settings. Source-
ranked actual RPO/traversal, demand transport, return/first traps and ABI entry
derive the existing Scalar.Domain for arbitrary-length forward jump/return CFGs.
No accepted-input certificate or all-values-materialized premise is added.

The same 4,543-symbol paired comparison remains 900→900 exact with no losses and
four changed instances. Ten newly eligible captured instances are all two-block;
the provider selects actual Stock for 273 instances after CLI legalization.
The same ten cases with existing regalloc2 remain 0→0 exact. The changes remove
duplicate cmp/cset in wrapping add/sub, with carry selection still different.
These are bounded measurements, not completion percentages or allocator changes.

Continue actual ordinary conditional, bit-test/table and critical correct-choice
source simulations; then inherited loop values, memory/addressing/atomics,
calls/exceptions, uncovered reachable families and original-domain whole-driver
simulation/Stock-only/downstream completeness. Saved next code already derives
actual brif calls and source-condition provenance, and proves a witnessed
boolean-companion-to-branch semantic replacement using Std3. Connect these to
the actual emission/body/alias/CFG/ABI consumers; do not rebuild existing scalar
condition or per-edge prepare/spill/copy proofs. Preserve first traps and source
fuel/definedness, original inputs, old variants, axioms, identities and stages.

A same-input source inventory finds 1,695 brif instances but only four with
current scalar bodies, original checks and source-forward control. Control
composition remains required; effects/memory/calls are essential for broader
coverage. Backedges require original SSA/dominance and carried-value invariants
beyond forward demand order. No first-class/proof-fragment stop or wholesale
prerequisite queue. Improve the shared-checker validation boundary when it fits
a substantive batch, retaining all old gates and exact axiom sets.

Keep #44 and concrete #140 interface coordination current. Reconcile each batch
with main, push backups and squash-merge promptly after author gates. Keep one
warm cache and bounded builds; archive unique evidence before deleting completed
outputs, and preserve all dirty/unpublished source. Full original #140 remains
open; fallback is acceptance preservation, not completeness.

## Conditional source domain checkpoint (2026-10-27 UTC)

The next implementation branch now proves the first legacy-compatible wide
entry-parameter conditional class through actual selected direct/synthetic copies,
scalar return leaves, instruction-zero ABI entry, returns and first traps. The
source selector derives the unchanged Scalar.Domain and checker soundness;
legacy edge-copy compatibility is proved internally. Complete original returning
and reachable-divide-by-zero witnesses compile and execute. See
[conditional progress](../research/stock-conditional-cfg-progress.md) for exact
1190-key/108-root validation and the two fixed-example native input-check axioms.
PR #635 activates this class in the shared default compiler/checker/linker and
generated-proof consumers, appending route9 with0–8 retained and complete prior
ForwardCfg pipeline fallback. All author gates pass on31a1befe; see
[terminal evidence](../research/stock-conditional-cfg-production.md). Same-input
agreement remains900→900/4543, with no losses or changed bytes. Continue the
prepared ranked conditional tail class, general conditions/per-edge/loops and
effects/calls/full-domain obligations. No proof-fragment or first-class stop.
Broader control/per-edge/loops/effects/calls/full-domain obligations remain open;
this first conditional class does not replace them.

## Starting point and next deliveries

Arithmetic shipped in #356 (95b87108); complete add/sub/select activation shipped
in #357 (ba08bcaf); the bounded maintained runner shipped in #358 (40333cb4).
The complete AND/OR/XOR extension landed in #359 (779bc7ba), exact squash
tree verified against validated 0d9f54fe plus its documentation receipt. [Logical activation evidence](../research/stock-logical-production-activation.md)
records current normal/trust/runtime/native/CLI/retention/identity/example gates,
exact original axiom/header parity and actual provenance. The actual squash and integrator notice are recorded in #44/#140/#261.

Continue remaining scalar classes, including real trapping
division/remainder, using complete saved source wrappers and shared consumer composition. Read
[the obligation ledger](../research/stock-driver-obligations.json); historical root
inventories require current-source/scope reconciliation and are not coverage
percentages. No whole-backlog port or new worktree is needed. Canonical saved work and terminal logical evidence are backed remotely at29f6be2f.
The superseded logical view was archived, its unique dirty recovery source pushed
atfc1bb8e1, and the clean view removed. Four necessary views and one warm cache remain.

The constant selected-record/body prerequisite landed in #360 (22a05d3b), with
all 2,659 normal keys, 45 trust audits, previous 1,322 axiom sets and both old scan
headers preserved. Its complete source/csem/body witness is standard-only; evidence
is backed remotely ataeaaf5e5. See the constant record/body research receipt.

Constant production activation is complete through one reusable scalar consumer.
[Terminal evidence](../research/stock-scalar-production-activation.md) records all
35 primary command gates and seven ownership records, exact previous axiom/header
and identity/stage parity, native byte execution, all retained classes and verified
examples. Validated source edfe4f4f is backed remotely with terminal evidence at
fe81690d. A universal internal Scalar.Domain is derived by fixed source-check
soundness. Shared pure source and ABI composition retains old variants; MOVK has
its own scalar read boundary, with the old check and cleanup whitelist unchanged.

Default attempt order is Scalar→Logical→Mixed→Arithmetic→legacy. Actual retained
artifact reconstruction probes every route against bytes and records its index,
on the original source/settings. Routing data does not restrict source theorems.

The NOT extension is complete through the same scalar consumers, with all17
primary command gates/eight ownership partitions, exact1378oldAXsets/3oldheaders,
1176nativecomparisons, two32subcheckactualCLI/link/generatedcohorts and current
fullcorpus/encoder/identity/stage/examples passing. Validatedfa5468f4 and terminal
evidence are backed817b6526. See the NOT activation receipt. Old constant selectors
and theorem variants stay. General roots include shifted NOT, while shift-bearing
whole functions await the next shift source class.

Multiplication/fused multiply is complete through the same scalar consumers.
[Terminal evidence](../research/stock-mul-production-activation.md) records20primary
gates/11ownership partitions,1399oldAXsets/18oldheaders exact,1344nativecomparisons,
two32subcheckactualCLI/link/generated cohorts, original flat-multiply artifact
retention and all current full gates. Validated1cd9816f and evidence backed9c3f26fd.
Reusable source classification/record dispatch/no-trap facts avoid copying earlier
families. Old selectors and theorem variants stay.

The complete shift class passes all author gates through the same scalar
consumers. [Terminal evidence](../research/stock-shift-production-activation.md)
records18primary gates/13ownership partitions,2728normalkeys,1470audited roots,
1428oldAXsets/34oldheaders exact,1512native comparisons, two32subcheck actual
CLI/link/generated cohorts, original flat-multiply retention and all current
full gates. Validatedca069aa6 and terminal evidence are backed remotely at
de6aae6e. Current source dispatch proves eight reachable shift roots;
historical counts are not semantic coverage. Both fused bitfield cases,
guarded source/body/entry-return/no-trap and ABI producer support are complete.
Old selectors, theorem variants and cleanup behavior remain.

Cast activation passes all author gates through the same scalar consumers.
[Terminal evidence](../research/stock-cast-production-activation.md) records
18primary/15ownership gates,1506auditedroots,1470oldAXsets/43oldheaders exact,
1680native comparisons, two32subcheck actual CLI/link/generated cohorts and all
current full gates. Validated845327d4 and terminal
evidence backed60dab84b. Actual808/819/946 execution and
source-derived exclusions for810/811/815/824 compose full body/entry/default
production. All prior selectors and theorem variants remain.

Negation, CLZ/CTZ, bit reversal/byte swap and rotations pass author gates through
shared scalar consumers. [Terminal evidence](../research/stock-bit-production-activation.md)
records 18 primary / 17 ownership gates, 1,541 audited roots, all 1,506 old axiom
sets / 45 old public headers exact, 2,064 native comparisons, two 32-check actual
CLI/link/generated cohorts and all current full gates. Validated source
`ab08eefa`; terminal evidence backed at `9f4c6d0e`.
Saved instruction-derived transfers and shared composition are reused; all old
cast variants remain alongside the more general source-format variants.

Popcount passes author gates through the same scalar consumers.
[Terminal evidence](../research/stock-popcount-production-activation.md) records
18 primary / 19 ownership gates, 1,571 audited roots, all 1,541 old axiom
sets / 29 old public headers exact, 2,256 native comparisons and two 32-check
actual CLI/link/generated cohorts. Validated source `13696563`;
terminal evidence backed at `6e9e92da`. Existing numerical/helper proofs
and original scope closure are reused; old variants remain. Existing complete source-transfer witnesses cover all four scalar
widths; production activation is i32/i64.

Signed/unsigned min/max passes author gates through the same scalar consumers.
[Terminal evidence](../research/stock-minmax-production-activation.md) records
22 primary / 21 ownership gates, 1,601 audited roots, all 1,571 prior axiom sets /
30 old headers exact and 2,448 native comparisons. Current and retained actual
CLI/link/generated cohorts each pass32 checks. Validated `3f52b679`;
remote evidence `1559dcb9`. Existing complete source wrappers, original
operand-type derivation and actual SameWorldNF framing are reused.

Measured ordinary native fixture runners retain identical checks/artifacts and
reduce repeated interpreted runs from minutes to about10 seconds. Keep the
interpreted default and explicit native mode, validate target keys/binary hashes,
and compile generated proofs freshly. Reuse existing complete source wrappers
before introducing another proof chain.

Integer comparisons and real cast-of-icmp811 pass author gates through shared
production consumers. [Terminal evidence](../research/stock-cmp-production-activation.md)
records22 primary/23 ownership gates,1675 audited roots, all1601 prior axiom sets/
35 headers exact and2640 native comparisons. Both current/retained actual
consumer cohorts pass32 checks. Validated `1dd7631f`;
remote terminal evidence `d5788ea0`. Real CSET normalization,
restricted original DFG operands, actual retained binding and memory-only cast
variants compose mixed body/entry/return without excluding IntCompare syntax.
Existing comparison numerical/helper proofs and all old theorem variants remain.
All original identities/stages and ten prior native grids are retained.

Signed/unsigned high multiplication passes author gates through shared consumers.
[Terminal evidence](../research/stock-highmul-production-activation.md) records
22 primary / 25 ownership checks, 1,732 audited roots, 1,675 prior axiom sets /
32 public headers exact, and 2,832 native comparisons. Both current/retained
consumer cohorts pass32 checks. Validated `16a5f963`; remote
evidence `8abeffdf`. Complete existing highmul source transfer and
shared composition are reused. All prior computations, identities and stages remain.

For an isolated fixture repair or additive main reconciliation, preserve original
record source heads. Carry unaffected evidence only after checking the exact
source delta, import closure and unchanged relevant executable hashes; rerun
current normal keys/trust, affected executable ownership and affected consumer
cohorts. Never relabel historical passes. Unknown dependencies require reruns.

The complete singleton returned division/remainder class passes current author
gates at `b1ef0c67` on `5c1351a0`, reconciled onto `aa81ed96` with documentation
changes only. [Current and historical evidence](../research/stock-div-production-activation.md)
records25 primary/27 ownership gates, actual normal/trust/native/runtime/encoder/
identity/stage/consumer/retention/verified-example observations and remote
backup `a2c9d0d8`. Every actual record retains its source head.
The default compiler/checker/linker/generated-proof consumers include all four
operations and real zero/overflow traps; original arbitrary operands/slots and
old pure theorem variants remain. Source bridges retain8/16/32/64; production
activation covers32/64 across six ABIs, both cleanup modes and both real allocators.

The complete mixed scalar-prefix/final-returned division class now passes author
gates on1239f8bc, directly based on mainef499aca and independent of performance513.
[Terminal evidence](../research/stock-mixed-div-production-activation.md) records
actual source heads, full return-and-trap domain,96complete pipeline/source
witnesses,6192native comparisons, both32checkconsumer cohorts, exact previous
axiom/header/identity/stage parity and retained artifacts. Safe signed-divisor
root IDs790/791 are observed. All prior theorem variants and inputs remain.
Full140 continues immediately with arbitrary-position/undemanded/sunk division
and every original remaining obligation; no stop at this class.

Arbitrary-position unused, consumed and multiple i32/i64 divisions/remainders
pass all current author gates through the shared default consumers in #611.
[Terminal evidence](../research/stock-general-div-production-activation.md)
records validated code `cd57ac63` on main `1510186e`, all 3,947 normal keys,
19 audits/577 public roots, 33 ownership partitions, exact old axiom/header and
identity/stage parity, actual native execution, current and retained CLI/link/
generated proofs, all six full gates and both verified examples. Terminal evidence
is backed at `69182545`. The original nine arguments, source slot, arbitrary
operands and zero/overflow traps remain. This completes this production class;
full original #140 and general register agreement remain unfinished.

Original i8/i16 scalar production coverage now extends the same default shared
consumers. [Narrow activation evidence](../research/stock-narrow-production-activation.md)
records validated `a1b29bf7`: 474 complete positive pipeline configurations,
8,532 native executions, actual ordinary compiler CLI bytes, current/retained
consumer cohorts, 38 ownership partitions, all six full gates and both verified
examples. Old selectors/theorem variants, exact old axioms, input conditions,
accepted identities and successful stages remain. The original i8 byte-swap
scope rejection stays explicit. No new class uses a separate compiler stack.

Production applicability remains important: the ordinary CLI retains its
no-opt/no-TryCall input-file guard. `cargo-fv` compiles each function in its own
file, so a try-call function does not disable unrelated pure Rust functions.
The allocator default remains Lean. Fresh real-example agreement remains
887/4,543 symbol comparisons; these class gates are not general register
agreement or Stock-only completeness. Track these separately from proof counts.

Bmask/nop production activation landed in #624 (`ab1abdfc`) through the same
shared scalar/division compiler/checker/linker/generated-proof consumers.
[Activation evidence](../research/stock-mask-production-activation.md) records
all sixteen independent source/result width pairs, actual native and ordinary
CLI behavior, retained artifacts and full original identity/stage/axiom parity.
This is a completed production class; general CFG and register agreement remain
unfinished. Continue original control/successor arguments/critical edges/loops,
memory/effects and calls/unwind through the fixed obligations below. Keep legacy
fallback until the complete original input domain and downstream consumers are
proved. Do not remove production guards without the corresponding proofs.

A concrete build boundary can be delivered alongside the next implementation:
extract unchanged VCode outcomes, their prefix lemmas, ArgsAtEntry and Reach into
a stable interface; retain names/definitions and LowerSim re-exports. Isolated
interface/PrepareSound/Statement/LowerSim copies compile; full affected gates
are still required. Coordinate the shared-file boundary on140. This avoids
rebuilding generated interpreter proofs after unrelated simulation additions.
Do not stop at either this first trapping class or a performance-only packet.

Next: complete original widths/ABIs and remaining pure-family cases; broader
colored/sunk instructions; every unchanged original #140 control/
memory/trap/effect/call/source/block/whole-driver/completeness/consumer obligation.
Never exclude original accepted compare/cast syntax to simplify composition.
Universal successful lowering and downstream completeness remain. Fallback is
not Stock completeness; full original #140 remains unfinished.

The CFG dependency packet derives quiet records and shared family/body execution
for arbitrary original blocks, executable return/later-trap witnesses, and
source consistency through actual successor binding. [Validated evidence](../research/stock-cfg-body-checkpoint.md)
records3,984normal keys,79audit files and626exact prior axiom sets. All existing
Lean sources/import keys remain intact; additions use isolated modules.
Production CFG activation remains pending. Continue machine branch execution,
actual guarded successor demand/value/world transfer and the existing per-edge
preparation/consumer stack, then critical edges/loops and all original obligations.

## Maintained validation runner (landed #358)

Use scripts/stock-delivery-gates.py with plan/run/resume/report commands around
existing build/audit/runtime/integration/native/example scripts. No replacement
scheduler, compiler redesign or workflow platform. Split independent current and retained
integration cohorts into separate one-gate manifests up front so they can use
both available slots after full/example gates; preserve the aggregate16GiB/two-job
limit. Never mutate a running manifest or duplicate a healthy cohort. Manifest records base and
candidate, module/consumer changes, explicit gates and complete declared input
fingerprints (sources/import outputs/tools/settings/scripts), theorem/header and
identity baselines. Unknown dependencies require conservative reruns.

Persist each command/exit/assertions/log and output hashes/provenance atomically.
Resume only successful input-matching intact evidence; distinguish a failed gate
from failed reporting. Use normal Lake keys, never manual hash rebinding. Keep
generated fixture/CLI proof modules in one import root. Test injected command
failure, changed inputs, corrupted output, interrupted reporting and resume.
Import Mixed's receipt as historical evidence without relabelling or rerunning.
Further tooling only fixes concrete delivery blockers.

## Dependency-ordered proof and production work

The reconciled logical packet supplies arithmetic/select/logical composition,
retained binding, guarded source transfer, arbitrary-value body/entry/return and
world-NI proofs, classifier soundness and actual default consumers. Continue the
following sequence through the full goal, extending shared proofs and existing
parametric consumers; retain old interfaces and theorem variants.

Maintain one obligation ledger over current actual rules/helpers/terminators/
traversal/consumers, each linked to its proof or scope-exclusion theorem,
composition requirement, witness, production coverage and completeness status.
Inventory counts do not prove coverage. Fixed remaining order:

1. Remaining pure scalar families: constants, NOT/fused logical forms,
   multiplication, shifts/casts, counts/rotations/reversals, comparisons/min/max,
   high multiplication, division/remainder and reachable look-through cases.
2. Control flow: branches/successor arguments/critical edges/block parameters/
   loops, retaining per-successor edgeArgs through preparation/allocation.
3. Memory/traps: addressing, loads/stores, stack/global/symbols, atomics, trapping
   execution and omitted/sunk effects under current memory/world contracts.
4. Calls/exceptions: direct/indirect/GOT calls, ABI/sret/reserved-result values,
   TryCall continuations and unwind metadata.
5. Whole-driver closure: source/scan/block/original-synthetic-node/traversal
   simulation, all completeness and remaining production consumers.

For every family reuse saved proofs and mainline machine lemmas. Derive matching,
request success, retained bindings, source availability/typing/demand/state and
execution obligations internally from original input conditions. Extend shared
body/scan composition, factoring only duplication actually encountered; do not
copy a compiler/linker/proof stack for each class. Carry completeness alongside
class correctness: prove selection/request success and downstream-domain facts,
or record the exact outstanding obligation. Fallback is not Stock completeness.

Each packet enables a complete production class or closes a named dependency for
the next class/whole-driver theorem. Land dependency-closed reusable prerequisites
without waiting for every family. Land ready packets before starting another.
Do not combine individual legacy/Stock instructions without proved shared
invariants. No output-equality/fixture allowlist/corpus replaces universal proofs.

## Validation and landing

Follow current docs/TO-PROVE.md section7 author per-PR gates. Replay normal
FV/FVTest keys with the bounded scheduler and affected tools; audit new/changed
roots, owned/generated constants and affected E2E dependencies. Preserve old
headers and exact required axiom sets. One bundled MCP review per proof packet;
no redundant per-theorem loops. No sorry/admit/new handwritten axioms or stronger
public input premises.

Run runtime/encoder for lowering/preparation/allocator changes, E2E/link for
consumer/scope changes, CLIF/optimizer checks for semantics changes, and verified
fv-demo/survey for driver changes, including applicable crate proofs. Retain
both cleanup-mode original 1150/prior accepted identities and ordered stages.
Activation additionally checks actual raw success, real settings-matched oracle
answers/negative controls, complete transactional retry, all prior classes,
native emitted-byte execution, real CLI/link/generated proofs and trust scans.
The selector is internal; unsupported input/failure retries the same original
input/settings before publishing artifacts. Consumers must prove the actual
selected artifact. Preserve the executable/proof import boundary.

Reuse successful evidence only with complete verified input equivalence and
original provenance. Failed gates never count. Fetch current main before landing,
reconcile and rerun affected gates for nontrivial changes. Open non-draft PRs and
squash promptly after author gates; do not wait for CI or continuous full-main
validation. Notify integrator of actual squash. Fix/revert attributable reds
before more expansion. Full validation stays continuous on main, not an extra
full-from-scratch author queue.

## Completion and operating rules

Finish all alias/fresh/reserved values, omitted/sunk effects, rule/helper
execution/exclusion, memory/trap/exception invariants and original-domain driver
simulation. Prove Stock-only lowering success, preparation/allocation/checker/
physical/encoding/production completeness; finish optimizer/cleanup/unwind and
all consumers. Retire rollout fallback only where Stock-only correctness and
completeness justify it; retain required legacy interfaces/theorem variants and
additional current-main acceptance. Do not silently enlarge/shrink #140's domain.

Before closing #140 run final full current-source FV/FVTest/tools/crates/trust,
runtime/encoder, both cleanup identity/stage reports, fresh complete settings-
matched Stock comparison, generated proofs and verified default-linked examples.
Corpus success supplements proofs. Track proof landings, actual production
coverage, remaining legacy routes and completeness separately.

One active implementation packet and at most one dependent review packet. Port
only the next closure. Read contributor statuses/claims and update #44 before
work, after commits/scope changes/stops. Flag concrete overlapping interfaces
in #140 and pause only conflicting work. Reuse mainline models/contracts/proofs.
No new subagents without explicit authorization.

Use existing delivery view and one warm cache, 16 GiB aggregate/max2jobs and all
memcap/OMP limits. Preserve healthy kernels. Keep 100 GiB free target/50 GiB minimum.
Push meaningful source checkpoints; archive unique evidence incrementally, retain
provenance and verify backups before cleanup. After each batch remove unneeded
clean views/outputs; preserve dirty/unpublished source and unique evidence.
Roughly 8 substantive PRs/day is pacing, never a quota or reason to fragment.
Record implementation/porting/validation/operational-repair time. No routine
confirmation; keep working until every original #140 obligation is complete.

## Current delivery boundary and next mixed-body work

Singleton returned division/remainder shipped in #512, squash6a80a595. Complete
scalar-prefix/final-returned division passes the actual author gates on1239f8bc,
directly based on current mainef499aca, for #521. Its terminal receipt links
complete remote evidence9140614f. Both classes use the shared default consumers;
old variants, arbitrary original values and actual traps remain.

Independent exact-body outcome/value import refactoring #513 remains under its
own affected witness validation, with source5aae55c3 preserved. It does not block
production implementation delivery. Static import-graph improvements are not a
measured wall-clock speedup or a completed correctness gate.

Continue with arbitrary-position/undemanded/sunk division and colored source
instructions, reusing actual record/result bindings and the new generic scan
return/trap composition. Derive retention and deferred-effect obligations from
original SSA and actual selection, rather than adding accepted-input premises.
All original #140 effects, calls, control, widths/ABIs, block/whole-driver
simulation and universal Stock-only/downstream completeness remain active.
Fallback and successful Stock.lower do not establish Stock completeness.


Returned-definition retention is now proved across arbitrary original source
positions on27003599/current-main61934c30. [Evidence](../research/stock-returned-definition-retention.md)
records682normal keys,20audited roots,134standard-only core/16fixed-witness
constants and a complete non-final-division source witness. All old variants and
existing consumer imports remain. Continue immediately with the generalized
source return/trap domain, classifier and default consumers; this dependency
alone is not broader production activation or full140completion.

## Returned division at arbitrary scalar body positions

Implementation `b1990ec02ff083882720dcc436d638c0db5f2b04` passes the current author gates; [terminal evidence](../research/stock-returned-div-production-activation.md) records the actual results and remote backup. The arbitrary-position class extends the default shared consumers while keeping old selectors, theorem variants and original inputs. Full #140 remains open; next derive genuine sink exclusion for unused/consumed division and continue every original effect/control/whole-driver/completeness obligation.

Actual generated-program no-load sink exclusion passes normal/trust/witness
checks at `bc53c102` on main `66f34776`; [evidence](../research/stock-no-load-sink.md).
All four sinking matches are excluded and complete helper execution retains
the sunk array regardless of result demand. This closes an interpreter dependency,
not production activation. Continue source-derived contexts and full driver
retention before unused/consumed/multiple-division activation; full #140 remains.

The arbitrary scalar/division source prerequisite passes fresh current-main author
gates. [Source/driver receipt](../research/stock-general-div-source.md) records
source-derived complete unsunkness independent of demand, actual result binding,
guarded body/entry return and trap composition, and complete critical-edge/source
witnesses. Old consumers and theorem variants stay. Next immediately activate
unused/consumed/multiple divisions through the existing shared production route;
then continue every original #140 obligation. This prerequisite is not production
activation or whole-goal completion.

## Bmask/nop production delivery (2026-10-25 UTC)

Implementation `0aecff7c` passes all24 current readiness requirements and enables
bmask/nop with independent four-width source/result types through the existing
scalar/division compiler, checker, linker and generated-proof consumers.
[Activation evidence](../research/stock-mask-production-activation.md) records
3,976/3,976 normal modules,12nativeobjects/3,888byteexecutions,70ownership
partitions,exact old axioms/headers/identities/stages and verified examples.
Fresh paired real-crate agreement remains887/4,543symbol comparisons with no
gains or losses; no full-goal or corpus-improvement claim. Publication replay
keeps the implementation receipts on their actual source head.

Continue original ABI/reachable-helper obligations and the full CFG closure:
quiet original-block metadata/records, arbitrary scalar bodies, entry/branch
semantics, successor-specific arguments/critical edges/block parameters/loops,
and the existing per-edge preparation/consumers. Current scalar adapters reject
nonempty successor-specific tables; retain those vectors through proved
adapters. Then finish every original memory/effect/call/unwind, whole-driver and
Stock-only/downstream completeness obligation above. Preserve saved work and
remove the completed batch's unneeded clean worktree after archiving evidence.

## Canonical original-block machine jump composition (2026-10-25 UTC)

Implementation `22d1627f` derives one actual original core with its retained scan,
prepared terminator, ABI widths, assembly and returned resolved block. Its
source-driven return/trap contract executes the actual complete body and jump,
retaining source continuation fuel. A genuine entered-source two-block returning
witness supplies the guarded input without a machine-execution premise.
[Evidence and limits](../research/stock-cfg-jump-checkpoint.md).

This closes the body/jump dependency after #625; production CFG activation is
still pending. Next derive demanded outgoing and inherited successor values,
compose source DFG and actual per-edge copies into the guarded successor relation,
then critical edges/loops and every remaining original #140 obligation. Do not
replace the whole driver goal with this proof packet.

## Actual outgoing values and successor parameter binding (2026-10-25 UTC)

Implementation `49bf11e9` derives actual outgoing argument marks, mapping and
bounds through the same compiled block, obtains argument values from its actual
post-body guard, and executes the real per-successor copies to every target
parameter. The real entered-source two-block witness executes body/jump and
source successor binding before those copies. [Evidence and limits](../research/stock-successor-parameters-checkpoint.md).

Next establish the inherited nonparameter value invariant, including backedges
whose successor demands arise later during reverse compilation, using the saved
source availability and available-value fresh-write frame results. This is an
internal dynamic simulation obligation, never an additional accepted-program
certificate. Continue complete guarded successors, synthetic critical edges,
conditional/table branches/loops, production activation and every original140
obligation; parameter binding alone does not establish those results.

## Inherited-value body/jump carry (2026-10-25 UTC)

Implementation `4c955f39` carries arbitrary already-held block-entry values
without a demand premise through actual source steps, selected constant writes,
complete constant/omitted/nop bodies and their actual jump. A genuine two-block
7+9=16 execution witnesses the entire next-scan guard after real source binding,
per-edge copies and inherited/DFG/memory transfer. [Evidence and limits](../research/stock-inherited-carry-checkpoint.md).

Next reuse existing scalar/division record write bounds/frame results to extend
carry; derive whole-edge demand/order coverage for new definitions and backedges
internally. Continue arbitrary guarded successors, critical edges/loops, actual
ABI/return and prepared/physical consumers toward substantive production CFG
activation, then every original140obligation. Production CFG is still inactive;
this witness does not replace the arbitrary-function theorem or physical entry.

## Division/mixed-body carry and next production boundary (2026-10-25 UTC)

Implementation `e91b7103` reuses the existing division source execution/frame
for all old signed/unsigned/narrow/remainder cases, retains zero/overflow traps,
and composes complete constant/division/nop bodies under carry, including unused
and multiple divisions. Three real entry/normal/trap/body witnesses add no finite
facts or native axioms. [Evidence](../research/stock-division-carry-checkpoint.md).

Next prioritize actual return-block/core composition and a substantive two-block
CFG production class through actual ABI/return and prepared/physical consumers,
using the now-proved prefixes/jumps/per-edge copies/carry. Do not turn every
remaining carry family into a wholesale activation gate. Continue successive
function classes, broader scalar carry, whole-edge demand/order coverage,
critical edges/loops and every original140obligation after that first activation.
Production CFG remains inactive until its current proof/consumer gates pass.

## Complete first CFG source class (2026-10-25 UTC)

The direct two-block class now has general instruction-zero return/trap
simulation, actual same-core ABI entry, internally derived successor coverage,
complete return/zero-divisor witnesses and an executable source/artifact check.
Actual single-successor vector equality transports it to the existing
`Scalar.Domain`, including nonempty parameter copies. Full4031/4031 and20new
audited roots pass. [Evidence and exact limits](../research/stock-two-block-source.md).

Next close the concrete consumer boundary: existing ABI-read models exclude
`.goto`, so add a proved CFG variant with entry-only argument-read/control-flow
transport and realization. Keep old checks/models intact. Then wire and validate
actual compiler/checker/linker/generated-proof default production with legacy
fallback and land a substantive activation. Do not merge proof fragments as a
substitute or wait for every remaining function family. Continue successive
classes and every original #140 obligation after this first CFG activation.

## Active ranked conditional tails checkpoint

#635 is merged at91c809f7. The next substantive route10 implementation and complete source/domain/ABI witnesses are implemented; see [progress](../research/stock-conditional-forward-cfg-progress.md). Freeze and finish current author gates, preserving all prior fallback behavior and exact old theorem/axiom/input/identity-stage contracts, then squash and continue the remaining original #140 obligations.

## Ranked conditional tails author gates complete

PR #636 implements the route10 conditional entry/ranked-tail class on7170a146, with all current author gates passed; [terminal receipt](../research/stock-conditional-forward-cfg-production.md). Publish and squash under current author policy; retain the complete prior conditional pipeline and all original inputs/variants/axioms/identities/stages. The paired actual-output metric is900→900/4543, with no gains/losses/changedbytes. General ranked parameter-conditional return/first-trap/source-domain/ABI drafts are preserved outside this frozen packet. Continue those and computed/narrow conditions, per-edge/table/loops/effects/calls and original full140 obligations; no first-class/proof-fragment stop.

## Nonentry parameter-condition CFG delivery

PR #637, implementation `9f27ad6c3b13f3fd378693389e82e9cdaf616b65`, extends production through arbitrary ranked quiet scalar CFGs with original wide parameter conditions at later source blocks. [Terminal author evidence](../research/stock-parameter-cfg-production.md) records all gates; route11 retains0–10 and complete prior fallback. Conditional successor arguments remain empty. The actual paired comparison is 900→900/4543, with 0 losses. Continue broader control/per-edge obligations and actual-corpus memory/effects/calls; reuse existing memory primitives with mapped/guarded source variants and a memory-capable contract derived from ORIGINAL world premises. Preserve pure-domain variants and exact old axiom sets. Full original140 remains open: broader conditions and nonempty conditional copies, tables/loops, memory/addressing/atomics, calls/exceptions, uncovered families and original-domain whole-driver/Stock-only/downstream completeness. Fallback preserves acceptance and is not completeness.

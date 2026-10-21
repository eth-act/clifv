# Incremental Stock driver completion

Execution plan updated 2026-10-21 after the user's efficiency review. Supersedes
the historical ordering/checkpoints in this file and the recovery roadmap;
saved source and historical receipts remain preserved. Full original #140 scope
is unchanged: actual Stock source semantics, simulation/completeness, production
compiler/checker/linker/generated proofs, original inputs/theorem variants/exact
required axioms/accepted identities/successful stages.

## Starting point and next deliveries

Arithmetic shipped in #356, squash 95b87108. Complete single-block i32/i64
add/sub/select activation is validated at d7f93237 with 39author gates; see
[activation evidence](../research/stock-mixed-production-activation.md).
Source comparisons are not part of that class. Land this ready packet before
adding tooling or another class. Check current main; reconcile/rerun only gates
whose dependencies changed. Record the actual squash and notify #140/#261.

Next deliver exactly one bounded validation repair, then saved logical production
support. Use existing views/cache and preserve canonical driver-proof-resume,
stock-lowering and logical dirty work. Historical successes count only at their
real source/dependency provenance, never as unverified current-main passes.

## Bounded validation repair

Add scripts/stock-delivery-gates.py with plan/run/resume/report commands around
existing build/audit/runtime/integration/native/example scripts. No replacement
scheduler, compiler redesign or workflow platform. Manifest records base and
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

Reconcile saved logical work onto the actual Mixed squash. Reuse arithmetic/
select composition; finish AND/OR/XOR actual selection, retained binding,
availability-guarded source transfer, arbitrary-value body/entry/return/world-NI
proofs, classifier soundness, witnesses and all default consumers/fallback.
Extend existing parametric adapters; retain old interfaces as wrappers.

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

# Three-block Stock scalar CFG production

Validated implementation: `1a30db775fd41a3509633667b7d6d7d7524eae1d`, based on main`00576bd9` (#632).
This change enables the default compiler, checker, verified linker and generated
proof consumers for `entry → scalar body → return`, including nops and source
values inherited across empty-argument jumps. Full original #140 remains open.

## Source proof and production boundary

The actual reverse compiler traversal supplies coupled predecessor/successor
scans. Branch emission and outgoing marks retain demand. The successor guard
requires only its demanded available values; source availability and held-value
transfer follow internally from the original SSA/DFG facts. Dead/sunk values do
not become materialization obligations. Complete scalar/division/mask bodies,
both jumps, return and first traps compose from actual retained records, with
original source fuel and definedness. No forwarding-all-results or empty-body
restriction is added.

The same `Scalar.Domain`, `CompiledSemanticNI.cfg` and `ABIReadCfg` consumers are
used. The new complete provider retries the previous full provider on the
original source, allocator and settings. Routes0–6 remain; route7 is appended.
Existing optimizer/tail/exception eligibility and the default Lean allocator
remain. Original input conditions and theorem variants are preserved: all2,456
old backend proof files are byte-exact; allthree existing `CompiledSemanticNI`
public signatures are exact. There are no allocator/sharedLowerSim/CLIF-semantic
changes in this delivery.

Actual kernel-compiled fixtures return `rotate(7,1)=14` through two
empty-argument jumps and trap at a middle-block zero divisor. New general roots
use only `propext`, `Classical.choice`, `Quot.sound`; finite native facts are
labelled original-input witness checks. Two bundled MCP reviews report no
warnings; the trap witness adds only its fixed input-dominance fact.

## Terminal author gates

| Gate | Result |
| --- | --- |
| Full normal keys/current-HEAD replay | 4073/4073;76 rebuilt; healthy run43.2min |
| All trust audits | 92/92;3544 roots;all3518 prior axiom sets exact |
| Retained private ownership checks | 6/6 |
| New integration/generated proofs | 78 checks;18 global/per-entry roots;4 CLI roots |
| Retained scalar-entry/entry/CFG integration | 70/34/34 checks |
| Actual native grid | 24 objects;24000 byte executions;3000 Cranelift reference executions;0failures/disagreements |
| Runtime | corpus114/114;extra22/22;5755pass/0fail;existing unavailable cases retained |
| Encoder | 1398 identical;0differ |
| Both E2E modes | 1159 accepted;all original1150 and parent1159 identities/ordered successful stages exact |
| Verified examples | fv-demo21tests/2ELFs;survey53tests/18ELFs |
| Actual crate package | 93 modules;96 recorded commands;default package build passed |
| Same-input paired default allocator | 4543 symbols;900→900 exact;0gains/0losses;10changed function bytes |

The new runtime grid uses100 functions, allsix ABI configurations, both real
allocators and both cleanup modes, plus forced complete fallback and missing
oracle controls. It includes middle-block scalar families and direct inherited
results across empty-argument jumps, with an unused source constant.

The paired check ran both exact executables on immutable captured inputs while
other validation proceeded. After the ordinary Cargo examples rebuilt, all4543
actual candidate and reference function bytes/relocations, normalized inputs and
reported comparisons were checked against that snapshot. Reuse avoided a second
compilation of the same pairs; the actual example output remains bound to the
receipt.

## What changed in register agreement

All127 eligible normalized captured instances before the CLI's i128 legalization
pass source checks, actual Stock lowering and the read boundary, and select real
Stock code. These are captured instances, not unique-function coverage; the
pre-legalization diagnostic does not count extra CLI-legalized i128 cases.

Default-allocator exact agreement remains900/4543. Disassembly shows redundant
comparison/materialization instructions removed in the ten changed functions.
On those same ten inputs with the existing `--regalloc regalloc2` option, the
exact preserved parent executable matches0 and the candidate matches8; the
oracle, input and remaining settings are identical. The eight are saturating
arithmetic instances. The two leading-zero instances retain an instruction
selection difference. This diagnostic isolates a physical-allocation boundary;
it neither changes the default allocator nor reports a whole-corpus regalloc2
coverage result. A new source class is not a full-goal completion percentage.

## Evidence, recovery and next work

[Machine receipt](stock-linear-cfg-production.json) binds all gates to the exact
source head. Terminal evidence is remote at
[`c855548a02de199d2dd588c03f0d1c9d9ecd3346`](https://github.com/eth-act/clifv/tree/c855548a02de199d2dd588c03f0d1c9d9ecd3346/evidence),
on `agent/stock-cfg-body-progress-20261025T025359Z`:
`evidence/postmerge-manifest.json` and3 bounded archive parts. Concatenate the
parts in numeric order and verify archive SHA256
`c1e393458b7bb3a1a3a5b05db1bdb1f6435713694a3bfb9fe5636fe2d91801cd` before extraction. Source, exact parent executable,
immutable inputs, generated proofs, receipts, diagnostics and recovery metadata
are retained. The prior pending/failed snapshot remains in history at298e49a6.
No new worktree/cache/agent was needed;221MB of archived obsolete artifacts were
removed after membership/SHA verification. Dirty saved source remains preserved.

Continue arbitrary source-chain/acyclic CFG composition using the coupled actual
traversal and demand-aware successor transfer, then conditional/table/critical
edges, loop invariants, effects/memory/atomics/calls/exceptions, uncovered rules,
full original-domain simulation and Stock-only/downstream completeness. Reuse
existing `prepareAt`, per-edge preparation soundness/completeness and spill/copy
proofs; coordinate genuine shared consumer/interface changes through #140.
Backedges need an inherited-value invariant beyond forward-edge demand order;
existing scalar `CarryRel` preservation supplies a starting point. Fallback
preserves acceptance and does not establish Stock completeness.

The shared checker import currently rebuilds old large fixed witnesses when a
new provider is registered. Improve that boundary when it fits an implementation
batch while retaining current-default integration and every original gate; do
not replace source/production progress with another prerequisite queue.

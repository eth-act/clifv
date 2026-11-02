# Complete mixed fence integration

Status: source inspection and two additive drafts only.
No Lean command ran for the drafts.
The worker released the 1 GiB share before this preparation.
The verified local checkpoint remains `../140-fence-packet-v1/canonical-state-v2.json`.

## Exact source boundary

Keep `Backend.Stock.Proof.FenceFixture.function` unchanged.
Its seven statements are:

1. Load i64 from parameter7 at offset0 into value63, with default `heap_oob` flags.
2. Fence.
3. Add value63 and parameter31 into value100.
4. Store value100 through parameter7 at offset8, with default `heap_oob` flags.
5. Fence.
6. Divide value100 by parameter31 into value144, with unsigned division semantics.
7. Load i64 from parameter7 at offset16 into value128, with default `heap_oob` flags.

The function returns value128.
It has two ordinary i64 parameters and one ordinary i64 return under System V.
It has no calls, external declarations, or explicit stack slots.
Do not replace its trapping accesses, nonzero offsets, computed stored value, or division.
The old rejected `trapz` draft is historical evidence only.

## Old input and semantic conditions

Retain `LowerScope`, `Dominated`, `sigAbiOk`, and the original ordinary-return condition.
Retain `SourceEntry`, argument typing, and the actual source-to-register mapping.
Retain `Refines`, `DriverSem`, `MemRefines`, `MRStable`, `MemRelOk`, `MR`, and `ArgsAtEntry`.
Derive every record position, emitted decision, selected root, result binding, and final alias internally.
Do not assume that source value IDs equal register numbers.
Do not require a nonzero denominator.
Do not require `trapCode = none`.
Do not add a heap-validity predicate or execution certificate to source acceptance.

Keep the old memory-fault machine conditions `MapFaults` and `MapRelRW` in their existing semantic roles.
These conditions describe the source/machine world relation.
They do not become compiler acceptance checks.
Preserve all old explicit-trap, memory-fault, source, and peak-depth variants unchanged.

## Existing fault infrastructure

The source snapshot is the published892 tree `5b924d76`.
The observed main `5980cdfd` adds48 files and changes none of these fault sources.
The source-only bridge is `current-main-fault-source-bridge-v1.json`.
This bridge does not claim a current kernel gate.

- `FV/ArmFault/Step.lean:54` defines `MemMap`.
- `FV/ArmFault/Step.lean:72` defines `InstFaults` from actual instruction footprints.
- `FV/ArmFault/Step.lean:92` defines `execF`.
- `FV/ArmFault/Step.lean:96` defines `stepF`.
- `FV/ArmFault/Step.lean:139` proves that the all-permitted map gives the old fault-free step.
- `FV/ArmFault/Step.lean:150` proves the precise faulting step.
- `FV/Concurrency/ArmInstFoot.lean:89` supplies ordinary immediate load/store footprints.
- `FV/Clif/MemTrap.lean:33` already includes loads and stores in `Access`.
- `FV/Clif/MemTrap.lean:46` defines `MemTrapAt` with the real invalid source access.
- `FV/Clif/MemTrap.lean:52` restricts the old `memTrapInst` predicate to RMW/CAS.
- `FV/Backend/Proof/LowerSimMemTrap.lean:32` defines the atomic-only `VMemTrapFrom` boundary.
- `FV/Backend/Proof/LowerSimMemTrap.lean:38` composes its successful prefix.
- `FV/E2E/MemTrapStatement.lean:34` defines the qualified old `TrapsExplicitM` run condition.
- `FV/E2E/MemTrapStatement.lean:60` defines `MapFaults`.
- `FV/E2E/MemTrapStatement.lean:73` defines the actual `TrapAtF` observable.
- `FV/E2E/RegLevelMemTrap.lean:52` currently recognizes the atomic `ldaxr` faulting line.
- `FV/E2E/RegLevelMemTrap.lean:61` combines only `udf` and that atomic line in `TrapAtM`.
- `FV/Link/DeadCleanupExeMemFault.lean:38` supplies the target fault-aware executable theorem.
- `FV/Link/DeadCleanupExeMemFault.lean:65` supplies its peak-depth variant.
- Its source variants start at lines93 and167 and retain their existing `NoMemTrap` qualification.
- `FV/Front/RawExeMemFault.lean` supplies the corresponding bundle source/raw and peak variants.

Reuse this stack.
Do not replace the Arm model or weaken the existing contracts.

## Minimal semantic incompatibility

Consider an i64 function that loads from its sole pointer argument and returns the result.
Let the argument be0 and let the source memory contain no live allocation.
The default load flags give `heap_oob`, because `valid 0 8 = false`.

`IselContract.MemRefines` at line941 permits and specifies a successful machine load.
Its load clause has no source-validity or fault conclusion.
`MemRelOk` at line1107 constrains valid source accesses only.
For empty source allocations, its byte/valid/store obligations do not force an Arm fault.
The underlying Arm memory is total.
`ArmFault.stepF_all` explicitly gives a fault-free machine under the all-permitted map.

Therefore the unchanged generic assumptions cannot imply an explicit `VTrapFrom` for every source memory fault.
This is a source-inspection counterexample, not a completed Lean countermodel proof.
The existing architecture solves this with a reached-access boundary and a separate memory map.
`MapFaults` excludes the all-permitted-map counterexample at the existing semantic boundary.

## Additive draft interfaces

Only two new draft files are staged.
No shared-file copy changed.

- `StockMemoryAccessTrap.lean` adds `AccessAt` and `VAccessTrapFrom`.
- Its load constructor evaluates the actual addressing mode on load uses.
- Its store constructor excludes the stored value before evaluating the address uses.
- Its loop constructor embeds the complete old `loopTrap?` guarantee.
- Its prefix theorem composes actual VCode execution before the offending instruction.
- `StockMemoryFaultContract.lean` adds `DomainWithAccessTraps`.
- Its return clause retains the old memory-domain clause.
- Its trap clause separates explicit traps from a reached access with the original source address property.
- Its embedding retains every old `Memory.Domain` theorem through the explicit-trap branch.

The drafts prove no complete mixed domain yet.
They need actual current-context kernel and axiom gates after the share returns.

## Nonfence obligations

1. Derive the first load's retention across the fence from actual color/order and demand/sink invariants.
2. Reuse the zero-offset load source/scan theorem for its successful execution.
3. Reuse the actual iadd record proof for the computed stored value.
4. Reuse offset8 store record shape and retention with the computed value's original type and final alias.
5. Derive offset8 store fault addressing from the address operand, not the stored-value operand.
6. Reuse udiv wide success and original-source trap proofs without a denominator guard.
7. Generalize the existing offset8 address/retained-load proof to the actual offset16 final load.
8. Derive the return demand and both parameter mappings from original context and ABI facts.
9. Compose normal prefixes, explicit division traps, and load/store access boundaries in real source order.
10. Prove complete function returns and first traps under the additive domain.
11. Prove root and complete-driver progress separately; successful-run refinement alone is not completeness.

Reusable modules include `StockMemoryIntegerScanRefines`, `StockAluRecordValues`,
`StockMemoryOffsetEightStoreRecord`, `StockMemoryOffsetEightStoreRetention`,
`StockMemoryComputedStoreRecordSpec`, `StockDivUdivWideSourceValues`,
`StockDivSourceTrap`, `StockMemoryOrdinarySourceTrap`, and `StockMemoryOrdinarySourceContinuation`.
The old offset0/offset8 theorems remain unchanged.
Nonfence rule IDs and actual emitted traces still need measurement under the returned share.
The native witness currently certifies both actual fence records, not every nonfence selection.

## Production and shared boundaries

The current mixed-memory selector accepts exactly one zero-offset load followed by one zero-offset store.
Its old source conditions include notrap flags.
Its effect policy admits arguments, loads, stores, and returns; it excludes fences and division.
The CFG policy adds jumps only.
Do not weaken that policy before the complete new domain is proved.

Use new modules for generalized source fault classification, Stock access boundaries, domain proofs,
ordinary emitted fault-line recognition, and executable/bundle fault adapters.
Keep `memTrapInst`, `loopTrap?`, `VMemTrapFrom`, `Memory.Domain`, `ArmFault.stepF`, and all old theorems exact.
Add a fault-line observable that includes ordinary emitted load/store instructions.
Reuse the existing instruction footprints, permission map, and `ExecTrapF` result.
For the i64-only source class, derive legalization identity internally when connecting source fault results.
Do not impose the old load/store `NoMemTrap` qualification on the new additive result.

Future production wiring needs the coordinator's explicit shared-file boundary.
The protected CLI paths are `FVTest/Backend/Main.lean`, `FVTest/Link/LeanLinkMain.lean`,
and `FVTest/E2E/LinkCheckMain.lean`.
The current892 activation and worker-A's subsequent routing own those boundaries.
No draft changes those paths, route indices, the old fallback chain, or an allocator callback.

## Gates and cleanup

First validate the two additive interfaces and old-domain/atomic embeddings under the granted cap.
Then prove and audit all nonfence obligations before selector widening.
Run complete success and first-fault witnesses, including each trapping memory position and division.
Run raw/cleanup object, checker, linker, bundle, and actual generated-proof matrices.
Retain ordinary and peak source variants and the original axiom policy.
Preserve original byte-comparison inputs, accepted identities, and successful-stage maps.
The full normal/audit/runtime/filetest/encoder and original identity gates remain mandatory.

No cache, worktree, compiler, or shared source changed during this preparation.
The worker owns draft and prefix cleanup.
The parent owns publication, coordination, plan updates, and the current foundation build allocation.

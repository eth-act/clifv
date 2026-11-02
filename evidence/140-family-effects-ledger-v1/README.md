# Original #140 family and effect ledger

This inspection changed no compiler source and ran no build.
The source boundary is published #892 head `85b0aa1f`, tree `5b924d76`.
`ledger.json` retains every original row and reconciles all 517 names, IDs, and primary opcodes with current generated definitions.
`module-evidence.json` records current source hashes and theorem locations.

## Exact scope counts

`Backend.Stock.Proof.stock_source_root_partition_counts` proves 517=192+325.
The 192 roots remain in the ordinary-source closure table.
The 325 other roots have checked ordinary-source exclusions through `StockScopeRoots`.
The closure list also contains five branch rules. They are outside the 517 ordinary-root inventory.

`StockNonEOpsRoots` excludes 44 further roots for actual ordinary source statements.
`StockFloatMemoryRoots` excludes four more. These lists are disjoint.
This leaves 144 ordinary-source candidates after those checked exclusions.
These numbers do not measure execution proofs, reachable programs, or whole-driver completeness.
The original typed, float, tail-call, and unwind variants retain their own conditions.
No exclusion here removes their separate obligations.

The inspection identifies 24 candidate rows with concrete effect/ABI work:
14 direct atomic rows, one fence row, five address/global/TLS/stack-address rows, three call rows, and fused root 810.
The other 120 candidates retain existing scalar, memory, and trap class proofs.
This inspection does not discard those proofs or claim their arbitrary-mixture closure.
The number of fully closed original-domain rows remains unknown.
Each ledger row keeps that distinction explicitly.

## Atomic and barrier rows

| Actual root IDs | Generated family | Existing baseline proof | Actual Stock remainder |
|---|---|---|---|
| 983 | acquire load | `Backend.Proof.load_acquire_ok`, `atomic_load_ok`; `MemRefines` concrete load-acquire clause | Transfer helper execution through Stock state. Bind the fresh result and original address. Compose memory/trap behavior. |
| 984 | release store | `store_release_ok`, `atomic_store_ok`; concrete store-release clause | Bind actual source operands and retained writes. Preserve the exact changed memory and first-trap order. |
| 994–1004 | RMW add/sub/and/nand/or/xor/smin/smax/umin/umax/xchg | Eleven `atomic_rmw_*_ok` roots, `atomic_rmw_loop_ok`, `Backend.Proof.csem_rmwLoop` | Bind the returned old value, three fresh registers, and actual memory updates. Derive source/record/whole-body composition. |
| 1007 | CAS | `atomic_cas_ok`, `atomic_cas_loop_ok`, `Backend.Proof.csem_casLoop` | Bind comparison/replacement operands, the old result, two fresh registers, and conditional writes. |
| 1024 | fence | `fence_helper_ok`, `fence_ok` | Derive actual Stock record execution and scheduler barrier order. Lift it through source/scan/body and complete consumers. |
| 810 | uextend of atomic load | Legacy `uextend_atomic_load_ok` uses failed sinking | Do not transfer that exclusion. Prove actual Stock selection, acquire execution, deferred result binding, and first-trap behavior. |

The 25 primary atomic rows split into 14 closure candidates and 11 checked exclusions.
Those 11 are nine alternative RMW roots and two alternative CAS roots.
Fence 1024 is an additional candidate.

Stock already treats all four atomic instruction forms and fence as mandatory colored instructions.
`Backend.Stock.Proof.OrdinaryBody.actual_ordinary_source_step` already extracts their original source steps.
It does not establish that the machine produced their values or memory effects.
`StockScanSemantics` and `StockScanTrapSemantics` already compose supplied local obligations.
They do not discharge these missing atomic obligations.

The existing integer memory helper projection does not include terms 422, 423, 466, 612, or 613.
Those are acquire, release, fence, RMW, andCAS helpers.
Reuse the baseline contracts rather than repeat their ISA semantics.
The original memory model is single-threaded. This ledger adds no concurrency assumption or stronger contract.

### Root 810 requires special care

`rule_lower_1272` is root 810. Its RHS calls acquire helper 422.
Legacy `uextend_atomic_load_ok` refutes its legacy `is_sinkable_inst` behavior.
Stock deliberately revises this constructor.
`Backend.Stock.Proof.stock_loadSink_call_witness true` supplies a real positive atomic-load sink helper witness.
The witness alone does not prove reachable root 810 selection under an actual original-scope function. It prevents the legacy nonmatch from serving as a Stock exclusion.
The deferred-effect invariant must preserve the producer's load/trap before the consumer's result becomes available.

The coordinator reviewed this distinction again on 2026-11-02.
The witness name refers to an evaluator helper call. It does not identify a CLIF call.
The exact candidate uses an atomic i8 load and default flags.
Reachable root810 selection under the original Stock scope remains unproved.
The active worker must prove that selection before it claims this case as execution coverage.

## Calls, addresses, and stack arguments

| Rows or operation | Existing facts | Remaining distinction |
|---|---|---|
| Direct call 1031 | Actual source continuation/result-definedness; real direct-call witness; landed void-call andsret consumers | The consumed-result unit is active O work. General live values, multiple calls, andcallee effects still need complete composition. |
| GOT call 1032 | `Backend.Proof.call_got_ruleOk`, `call_got_lowerInstOk` | Retain the real GOT load, scratch register, indirect destination, result mappings, andoutgoing stack stores through Stock records. |
| Indirect call 1033 | `Backend.Proof.call_ind_ruleOk`, `call_ind_lowerInstOk`; typed variant in`IselCtlCallTI` | Preserve each variant's signature and parameter conditions. Lift actual callee-value mapping andsource/machine continuation. |
| Incoming stack arguments | `Backend.Stock.Proof.entry_loads_preserve_values`; nine-argument `stack_parameter_load_witness` | This is existing Stock progress. It does not establish outgoing call-stack arguments. |
| Outgoing stack arguments | `ctor_gen_call_args_gen`, `stackEnts`, `argsAt_after_stores`; typed `argsAt_after_storesC` | Current `StockVoidCallCheck.sourceB` limits arguments to 8. Derive the actual outgoing layout and memory frame under original conditions. |
| Function/symbol addresses 1026/1027 | `Backend.Proof.func_addr_ok`, `Backend.Proof.symbol_value_ok` | Bind actual Stock aliases and symbol addresses, then compose andactivate complete classes. |
| Stack address 1093 | `Backend.Proof.stack_addr_ok` | A source `stack_addr` is separate from injected incoming-argument loads. Derive slot bounds andsource/machine address binding. |
| TLS 1129/1130 | `Backend.Proof.tls_value_ok`, `tls_lower_ok`, `elf_tls_get_addr_ok`; qualified legacy Mach-O nonmatch | Lift the real TLSDESC state/results andpreserve the original model. A legacy nonmatch alone is not a Stock execution proof. |

The landed void-call check accepts one call with empty source results and empty returns.
Its retained code check requires a direct symbol call followed by empty returns.
GOT and indirect shapes do not satisfy that code check.
The current five-file consumed-result packet is proved locally but is not production activation.
This ledger does not duplicate that packet or A's control-flow work.

## Branch and exception supplement

The generated lower-branch table has eight rules.
IDs 1034/1035/1036 are direct, GOT, and indirect `try_call` variants.
They are outside the 517 lower-root inventory.
Their absence from the ordinary closure list proves no branch exclusion.
IDs 1132/1137/1138/1139/1140 coverthree `brif` roots,`jump`, and`br_table`.

Kev's `IselCallsOne` and unwind shape proofs already retain call and exception-edge structure.
`Link.EhCheck.Complete.unwCheck_complete` retains its explicit `tryRetsB` condition.
A qualified completeness theorem cannot silently replace an older theorem's conditions.
Actual Stock exception payloads, normal/exceptional source continuations, and unwind consumers remain full-goal obligations.
A owns current CFG/critical-edge/loop work. Coordinate exact overlaps only.

## Independent next implementation unit

After the active call unit, close the fence effect through actual retained records.
Start with a universal local theorem for any real fence record, not a new input classifier.

1. Project the unrevised fence/side-effect helpers with `Backend.Stock.Proof.stock_ctor_baseOnly`.
2. Reuse `fence_helper_ok` and `fence_ok` for the actual emitted instruction and machine frame.
3. Derive source and record refinement with no result-binding orheap guard premise.
4. Prove barrier ordering and normal/first-trap composition through existing scan interfaces.
5. Supply complete mixed-body, compiler, checker, linker, andgenerated-proof witnesses in both cleanup modes.
6. Activate the proved class with unchanged fallback and old variants, then continue all atomic rows.

This unit avoids A's control work and O's call-result work.
It closes one effect obligation. It does not replace original 140 with a fence classifier.
Acquire/release and all RMW/CAS forms follow with their real result and memory bindings.
Root 810 andgeneral deferred effects remain explicit throughout.


### Reviewed root810 fixture

The later StockAcquire810Witness proof establishes one actual original-scope fixture.
Stock.lower succeeds, and LowerScope and Dominated hold for the exact atomic i8/default-flags input.
Its retained instruction1 record contains fired rule810 and emits the original i8 acquire load.
The interpreter records a rule only after its right-hand side succeeds.
This fixed witness does not prove universal correctness, deferred binding, first-trap ordering, or production execution.
The review receipt is ../140-acquire-fused810-packet-v1/coordinator-reviewed-selection-v1.json.

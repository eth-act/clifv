# Stock memory source progress

The parameter-CFG production route landed in #637 at
`d5cc12ddeec71cc4ed77378812e9aca4fdfcba04`. Original #140 remains open.
This memory batch extends that implementation; it is not memory production activation.

`StockMemoryContract` adds a memory-capable source contract while retaining the
old pure contract and embedding every proved pure source. Its internal
`MemRelOk` premise comes from existing downstream world relations, such as
`E2E.memRelOk_holds` and `E2E.memRelOk_relW`. It adds no source-input certificate.
The old pure contract cannot express ordinary source loads: its arbitrary stable
memory relation need not connect source bytes to machine bytes.

`StockMemoryLoad` reuses source-load inversion, existing memory semantics and
byte/extension proofs without the legacy identity value/register invariant.
It derives an unscaled address from only the demanded mapped pointer, executes
the final-alias-resolved load, retains the memory relation and preserves every
register except its fresh result. `StockMemorySelection` proves actual ISLE
helper533 allocates and emits the decoded load while retaining scheduling fields
and its actual rule trace.

Positive witnesses use an actual dense Stock context, pointer register192,
fresh result194, a nonempty alias array and a live initialized four-byte heap
whose nonzero loaded value is `0xa5a5a5a5`. The memory/world premises are inhabited,
using the existing E2E relation and concrete `csem`; they are not discharged by
an empty allocation or a false memory relation. Actual helper selection is also
witnessed. All11 audited roots use only the standard axioms.

Focused maintained gates pass in `/tmp/stock-memory-load-gates-v2` against
the exact working source based on #637. Earlier failed attempts remain separately
recorded. These are focused module/trust gates, not a full production validation.

Next: actual root1043/address selection (the captured source chooses scaled
unsigned offset rule368), retained-record/result binding, guarded original-source
body/block/entry transfer, and the semantic memory read boundary. Then integrate
the compiler/checker/linker/generated consumers and run all affected author gates.
Keep all old theorem variants, required axiom sets, original source/world premises,
accepted identities, successful stages and complete prior-pipeline fallback.
General addresses/stores/deferred effects/atomics/calls/loops and original-domain
whole-driver simulation and completeness remain obligations after this batch.

## Selected record and guarded source transfer

The next checkpoint proves actual parameter-pointer address selection through
helpers575/574 and load root1043. Higher-priority look-throughs and the nonzero
offset alternative fail internally; rule368 supplies the unsigned zero-offset
mode. Actual retained-record/root receipts then derive the emitted load, fresh
allocation endpoint and final result alias. The guarded value theorem reuses
whole-run availability, fresh-register framing and demand preservation.

The complete original two-block fixture has standard-only proofs of scope,
SSA and dominance, with its inherited pointer proved available through the
existing greatest-fixed-point theorem. Its actual full Stock lowering supplies
the retained source/root receipts and installs alias193→194. A positive witness
executes that retained, resolved code on the live nonzero heap and transfers
guarded values to the actual original source-step frame after the load.
This does not yet prove a memory-capable whole-function domain or activation.

All4208 normal modules, the affected tools (5014 jobs), and98 audit files pass
in `/tmp/stock-memory-record-normal-gates-v1`. All27 new audited roots use only
standard axioms. Source compiler behavior and all prior theorem variants remain
unchanged. These checks validate the proof checkpoint; production integration
and its runtime/consumer/paired-output gates remain required before activation.

Next derive selected-root receipts directly from actual rule IDs and original
source metadata, lift the memory record through the existing guarded body and
entry/return composition, and discharge the semantic memory read boundary from
the original world relation. Retain full earlier production fallback and all
original #140 obligations; this checkpoint is backed up without a fragment PR.

## Actual selected-rule receipts

`StockMemorySelected` derives the original load's endian/data/type facts,
matches its actual root, and extracts typed RHS/named-root executions from the
real retained selected ID. `StockMemorySelectedValues` feeds those derived
receipts into the existing memory transfer. The earlier guarded nonzero-heap
source-step witness now uses this adapter, preserving its public statement.
No separate RHS/root/endian certificate is needed at this interface.

Focused maintained gates in `/tmp/stock-memory-selected-gates-v1` pass the
664-module closure and all32 audited roots, using only standard axioms. The
previous4208-module/98-file full validation remains the earlier checkpoint,
not a claim of full production validation for these additions.

Next adapt this transfer to the existing restricted-DFG guarded scan invariant,
derive pointer demand from actual marking and emission/unsunk classification
from the original source class, and compose whole bodies/blocks/ABI entry and
return. Then resolve memory read/NI transport and activate complete consumers.

## Existing guarded scan interface

The source-step adapter now uses the existing restricted-DFG invariant. Actual
marking and original dominance derive pointer demand/availability. It executes
the restricted source load, transports the result back to the original frame,
and retains source memory/slots without requiring every source value to be
materialized. The previous full-DFG and explicit-receipt theorem variants stay.
`StockMemoryScanRefines` discharges the existing `ScanFallRefines` interface,
including post-source DFG and the complete demanded-value/memory guard. An
inhabited indexed source/guard witness executes this interface on the live heap.

Current full gates in `/tmp/stock-memory-guarded-normal-gates-v1` pass:
4213 normal modules,5014 tool jobs,98 audit files and37 standard-only memory
roots. All prior audited axiom sets compare exactly; all32 earlier memory public
theorem headers and all2581 backend proof files from merged #637 are unchanged.
These remain proof checkpoints inside the next substantive production packet.

Next use the existing call-free `Clif.step_inst` semantics for source body
execution, preserving original fuel, frames, memory and later continuations.
The older `LocalBody.LocalInst` predicate excludes loads, so its current body
execution/entry wrappers cannot simply be instantiated with memory syntax.
Keep those variants and reuse their composition through an additive ordinary
source variant; do not strengthen the original input conditions or duplicate
machine/bit proofs. Actual source-family emission/sinking classification,
whole-body/block/entry/return composition and semantic read/NI transport remain
before production activation and its complete affected gates.


## Ordinary source execution and ABI composition

Six additive modules connect actual call-free source execution to retained body
scans and real ABI returns. The source execution theorem preserves the exact
residual fuel, source frame fields and terminator; it permits memory changes.
Existing pure/local variants remain byte-identical. The actual two-block fixture
now proves execution of its placed load-and-return block on the nonzero heap.
A separate single-block argument-return witness inhabits the new ABI entry
wrapper from PC0 with the live heap. These witnesses are separate: complete
PC0 control composition of the load function remains open.

Maintained checkpoint gates pass in
`/tmp/stock-memory-ordinary-normal-gates-v1`:4219 normal modules,5014 tool jobs,
98 audit files and49 memory roots with standard axioms only. All prior audited
axiom sets compare exactly; every previously published backend proof file is
byte-identical. Source/runtime/compiler behavior is unchanged. These are proof
checkpoint gates, not new production/runtime or agreement claims.

Next derive actual selected load IDs from original opcode/type metadata rather
than an explicit selected-ID premise, classify original source emission/sinking,
compose complete memory functions, then discharge semantic memory read/NI and
production consumers. Preserve the full original140 scope and earlier fallback.


## Complete first memory source domain

Original opcode/type metadata now derives actual load root1043. Additive guarded
adapters remove the selected-ID premise; the real placed load/return witness uses
that automatic path. Full actual load records preserve every sunk bit through
nested address selection and binding. More generally, every original definition
requested by its block return is retained and emitted through intervening scans,
including nontrapping loads. This reuses return demand and original source scope,
without a global no-load/no-sinking or retained-record input certificate.

`StockMemoryReturnBody` derives complete singleton load/return body refinement
from original syntax and a source parameter (including an inherited parameter).
`StockMemorySingleDomain` proves the full memory-capable entry/return/trap
contract for one-block i32 parameter-load/return functions. Nontrapping source
accesses preserve their existing stuck behavior on invalid inputs; no new initial
heap condition is imposed. The old pure and explicit-receipt variants remain.

`StockMemorySingleWitness` now instantiates that universal domain and actual full
Stock lowering at PC0: the original ABI parameter points to live nonzero heap
bytes, the load reads0xa5a5a5a5, and the actual ABI returns that i32 result. This
is a complete load-function witness, beyond the earlier separate entry/block
witnesses. Maintained checkpoint gates pass in
`/tmp/stock-memory-single-normal-gates-v1`:4229 normal modules,5014 affected tool
jobs and65 memory roots with only standard axioms. All49 prior memory axiom sets
and the changed witness's public header compare exactly; all other previously
published backend proof files are unchanged. The earlier full98-file audit
remains the ordinary checkpoint, not a rerun claim for this new snapshot.

No memory production activation or agreement gain is claimed. Next reuse the
existing initialized-byte/pair-world guarded-memory framework for exact read
transport and complete consumer integration, then extend to the captured two-
block/nop load-return class and further original140 families/effects/completeness.
Keep substantive delivery boundaries; these commits are backed checkpoints,
not fragment PRs. Preserve the full earlier production fallback.


## Exact paired reads on actual retained records

`StockMemoryReadTransport` derives full canonical machine-load equality from the
same initialized original source heap on both worlds. It proves exact paired
loads for ordinary and existing guarded (`MemRefinesR`) semantics, deriving read
permissions from source validity/readBits rather than a true read whitelist.
`StockMemoryPairedRecord` derives the selected root, emitted code, result binding
and final aliases internally, then executes the actual resolved retained record
on both worlds with one identical resulting virtual file.

Positive witnesses use distinct worlds, the live nonzero heap, the actual guarded
evaluator, and the real full Stock record with193→194 binding. All4233 normal
modules,5014 affected tool jobs,98 audit files and72 standard-only memory roots
pass in `/tmp/stock-memory-paired-normal-gates-v1`. All3971 prior per-file audited
axiom sets and all65 prior memory-root sets compare exactly. Published backend
and E2E proof source bytes are unchanged; additions are new modules plus audit.

Next connect exact paired guarded execution to the existing restricted-DFG
original-source postconditions by semantic inclusion, reusing the established
single-world transfer. Then compose memory bodies with ABI entry/return, complete
paired consumer and production activation, and extend beyond the first function
class. This checkpoint is not whole-function NI, activation, an agreement gain,
or completion of original140. All saved work and prior variants remain.


## Original source postconditions at paired worlds

`StockMemoryPairedSource` connects the actual guarded paired record to the
original source step and both complete postconditions. Semantic inclusion and
existing single-world transfer reuse the restricted-DFG, demand, frame, memory
and result-binding proofs. An indexed wrapper retains both original scan guards.
`StockMemoryPairedScan` supplies the existing `ScanFallRefines` interface at
`pairSem csem`, with the original RelW relations and initialized-memory Zof
agreement. Original relations derive read permissions; existing guarded lockstep
builds the paired run. No new accepted-source or world certificate is supplied.

An inhabited indexed source witness and a closed pairSem scan witness execute
the actual final code on distinct worlds and the live nonzero heap. Stack pointer,
no-error and constant TLS premises are explicitly inhabited. Maintained gates
in `/tmp/stock-memory-paired-source-normal-gates-v1` pass4235 normal modules,
5014 affected tool jobs and77 standard-only memory roots. All72 prior memory
axiom sets and both previous E2E witness headers are exact; every prior backend
proof source is unchanged. The full98-file audit belongs to the preceding381e
checkpoint and is not relabeled as rerun. The failed first gate attempt (missing
explicit masked-register decidability in a witness) is retained with the passing
retry. Compiler/runtime production behavior is unchanged.

Next share source-derived retained load-body data between the existing
single-world body/domain and paired body composition. Then complete paired ABI
entry/return and all production consumers, extend captured two-block/nop memory
functions and continue the entire original140 scope. No function-NI, production
activation, agreement gain or whole-goal completion is claimed at this checkpoint.


## Shared source derivation and complete paired bodies

`StockMemoryReturnSpec` derives one proof-internal retained-body packet from
original source syntax and original parameter membership. The preserved
single-world body/domain and new paired body consume the same packet. The
packet is generated by the proof, never supplied as an accepted-input filter.
`StockMemoryPairedBody` composes the complete actual body under pairSem with
both original source guards and initialized-memory agreement. Its live-heap
witness uses a real source step and inherited original pointer, rather than an
empty or impossible source relation. The old PC0 load-function and placed
load/return witnesses still compile through the shared derivation.

Maintained gates in `/tmp/stock-memory-paired-body-normal-gates-v1` pass4237
normal modules,5014 affected tool jobs and81 standard-only memory roots. All77
prior root axiom sets and every modified public theorem header are exact. The
previous381e full98-file audit is retained without a rerun claim. No production
compiler/runtime change, full function NI or agreement gain is claimed.

Next pair the existing actual ABI-return contract under the original MRP/RelW
world relations and reuse it with complete paired bodies. Then compose ABI
entry and the production compiler/checker/linker/generated-proof consumers,
extend beyond this first class, and continue all original140 obligations.


## Paired ABI return and complete placed block

The additive `StockMemoryPairedReturn` consumer executes the actual retained
return record under paired guarded semantics and preserves the original MRP
memory/world relation. `StockMemoryPairedReturnAt` composes ordinary source
execution, the complete paired body, actual placement and ABI return. The
nonzero-heap witness executes a real original load/return block in distinct
worlds and returns the loaded i32 value through the ABI.

Maintained gates in `/tmp/stock-memory-paired-return-normal-gates-v1` pass4239
normal modules,5014 tool jobs and84 standard-only memory roots. All81 preceding
memory-root axiom sets and all earlier public witness headers compare exactly
(`/tmp/stock-memory-paired-return-parity-v1.json`). The full98-file audit remains
the preceding381e checkpoint. This is a pushed implementation checkpoint;
paired instruction-zero entry, production activation and the full140 goal
remain open. The separate register-only paired entry draft is excluded from
this validation claim. Next finish that entry composition and connect the
actual production value-semantics and machine consumers.

## Current-main refresh (2026-10-29)

The saved memory packet remains unique relative to main `c533c22a`: there is
no mainline StockMemory source domain/paired initialized-load consumer. The
packet is ported on `agent/stock-memory-refresh-20261029`, preserving the newer
CraneliftInput/default allocator, frame/QA machinery, typed dispatch/placement
shortcuts and dead-cleanup generator. Four textual conflicts were resolved by
retaining those current-main paths and adding only memory cases. This is a
source port, not a current validation or merge receipt.

The old new-base service is inactive and its temporary receipts are gone.
Verified3753 metadata, original corpus sources and axiom logs were recovered from
remote archive `f95655a7d6f92c01c03ecc0fe13e024877adc4b1e77c5f2b8a3ccc0381afc360`
into durable `.git/agent-evidence/stock-memory-20261029`. Do not count the
interrupted52b22dc9 run as passed or relabel3753 evidence with a new source hash.

Current work first checks the memory-class closure, then imports compatible CI
cache outputs and checks paired witnesses/E2E consumers. Full per-PR author gates
remain required. Kev's open #756 supplies the known StockBlockScan startup-panic
fix before actual CLI integration; no duplicate witness patch is claimed here.

The next concrete coverage targets are four actual survey `h_dyn_generic`
functions: entry `nop; jump`, successor `nop; load.i32 notrap v0; return v2`.
Their original hashes match the preserved4,543-source provenance. This is a
measurable real-source target for extending the current bare one-block class,
not an eligibility/byte-agreement gain already achieved. See the active refresh
in [the delivery plan](../plans/stock-driver-incremental-delivery.md).

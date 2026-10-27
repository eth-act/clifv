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

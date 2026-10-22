# Stock signed and unsigned min/max in production

Validated source `3f52b67953f3f322190766eb244724201f7659d3`, based on main `80280f11`.
The default shared scalar compiler/checker/linker/generated-proof consumers now
support smin/smax/umin/umax for i32/i64, mixed with all prior classes. Original
input conditions, old theorem variants/selectors, exact required axioms,
accepted identities and ordered successful stages remain. The cleanup whitelist
and Arm/MInst/allocator models are unchanged.

## Reused source proofs and exact consumer boundary

Existing ScalarSelect min/max source wrappers supply actual matching, selection,
request/execution, retained binding and original guarded post-frames at all four
scalar widths. No alternate numerical/RHS proof chain is introduced. Existing
stock_lower_available_getAs_type derives the old explicit operand-type guards
from original availability/getters and restricted DFG typing. Runs already
supplies SameWorldNF, so the body proof uses that actual world frame directly.
Source formats derive the existing cast exclusions internally.

The universal body/entry/return/no-trap proofs construct the existing Scalar.Domain.
Existing first-match ordering selects roots 796/797/798/799 ahead of matching
fallbacks; historical root inventories are not coverage percentages. The actual
min/max witness exposed the old ABI check's zero-only comparison boundary.
A precise scalar comparison producer now handles the emitted register/register
and immediate SUBS forms, with flag framing, transport and machine realization.
All old ABIReadFlags and scalar selectors remain. Source getters/types and
comparison facts are derived internally, not new accepted-program certificates.

Complete mixed witnesses span six ABI configurations and both cleanup modes,
with arbitrary source inputs and the original arbitrary explicit slot. Four
register cases, positive/negative right constants and large left constants feed
an alternating add/xor aggregate; the final XOR keeps all previous computation
live. Actual selected roots and both comparison instruction forms are checked.
Existing source proofs continue to cover i8/i16; production activation is i32/i64.
Only two new fixed native facts enter witnesses; universal proofs stay standard-only.

## Validation and execution cost

All 22 primary gates and 21 ownership partitions passed on frozen source:
2,773 normal keys / 2,770 modules, four existing tools and four native fixture targets,
current crate keys, 53 audits / 1,601 roots; all 1,571 prior axiom sets
and 30 old public headers exact. Ownership covers 3,892 standard-only core /
945 fixed witness constants, 188 core / 29 witness /
20 executable owners and exactly 33 permitted native facts (previous 31 + 2).
One bundled domain MCP review reports only propext/Classical.choice/Quot.sound
and no source warnings.

All 24 objects pass 2,448 native comparisons / 612 Cranelift reference executions,
with zero failures/disagreements. All nine previous native grids and expected
results are exact. Real oracle, missing-binary and whole-attempt retry controls
remain. Current min/max and retained popcount actual CLI/link/generated cohorts
each pass 32 checks, including 33-function slices, reconstruction, stack bounds
and both preparation modes. Original flat-multiply bytes/proof sources remain
exact and current proofs compile in both modes.

Runtime: 4,737 passed / 0 failed, with the same 7 known non-runnable cases. Encoder: 1,321
identical / 0 different. Both E2E modes accept 1,159 / reject 0, retaining original 1,150
and prior 1,159 identities and ordered stages exactly. Verified demo: 21 tests /
2 binaries; survey: 53 tests / 18 binaries. JSON keeps command/log/output hashes
and original evidence provenance.

The unchanged popcount fixture was measured before min/max activation as ordinary
native executables: runtime 10.21s and linked 10.13s, versus minutes interpreted.
All 72 source/table/object artifacts and 12 ELF artifacts are byte-exact against
the validated interpreted run. The final candidate rebuilds its executables;
both actual integration cohorts run native with Lake-key and binary-hash checks.
The existing interpreted default remains; --fixture-mode native is explicit.
No fixture checks or proof gates are removed, and generated proofs still compile
fresh against current imports.

## Provenance, resources and remaining obligations

Early private-proof syntax/simplification errors and a failed pipeline witness
are preserved. The latter identified the actual comparison ABI gap and was fixed
before freezing author inputs. A draft assertion about an un-emitted ADDS form
was removed, together with that unused producer; emitted forms are checked.
Failed prechecks never count as passing gates.

Terminal evidence is remotely verified at `1559dcb90ef641c495426bb2d71ff8debf340a71` on
`agent/stock-minmax-evidence-20261022T023403Z`; archiveSHA256 `1224f054108dcd085c30d536a37545a18859a3e22babcc59019bd2e42a62e6a6`,
13,548,437 bytes / 1,396 files. Four necessary views, one physical
warm cache, over 700 GiB free and at most 16 GiB / two jobs. Canonical dirty recovery
source is untouched. Expendable generated outputs are archived before removal.

Full original #140 remains unfinished. Successful Stock lowering remains a
source-refinement premise; universal lowering/request/downstream completeness
is still open. Fallback is not Stock completeness. Next are integer comparisons,
including real cast-of-icmp811 (no narrowing of original accepted syntax), high
multiply/division/remainder, complete original widths/ABIs and all remaining
control/memory/trap/effect/call/source/block/whole-driver/consumer obligations.

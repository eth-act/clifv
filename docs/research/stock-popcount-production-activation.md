# Stock scalar popcount in production

Validated source `1369656323f4c5f8a121021a93298a6517b8b2a0`, reconciled onto main
`5e563a0b`. The shared default scalar route now supports i32/i64 popcount,
including combinations with every previously shipped scalar class. Original
input conditions, old theorem variants/selectors, exact required axiom sets,
accepted identities and ordered successful stages remain. The cleanup whitelist
is unchanged.

## Proof and production boundary

The existing complete original-source theorem is reused directly:
`ScalarPopcount.stock_lower_popcount_source_by_instruction`. It already derives
selection, operand reads, retained binding, fresh execution and the guarded
post-frame from the original successful driver and source step. Its existing
source-scope proof excludes i128/vector roots 941/942. All old popcount modules
and old witness modules remain byte-exact. Scalar roots 937/938/939/940 retain
existing zero/nonzero witnesses at i8/i16/i32/i64, with direct and prior aliases
and dirty upper machine bits. Body composition supplies its DFG relation
internally from the unchanged guarded source relation.

Stronger alternate variants developed during this batch are preserved separately
on `agent/stock-popcnt-scoped-alternatives-20261022` at `e2f15642`. They are not
required by this activation and are not included in the delivery packet.

Body/entry/return/no-trap proofs construct the existing universal Scalar.Domain.
The same compiler/checker/linker/generated-proof consumers use exact FMOV, CNT,
ADDP/ADDV and UMOV forms through shared ABI frame/transport/realization proofs.
No Arm/MInst/allocator model is changed. Whole mixed fixtures select actual roots
939/940 in six ABI configurations and both cleanup modes; prior computation stays
live, with arbitrary source inputs, an original arbitrary explicit slot, and a
ninth stack argument. Only two new fixed native facts enter witnesses; universal
compiler and source-transfer proofs use standard axioms only.

## Validation

All 18 primary gates and 19 ownership partitions passed on frozen source:
2,763 normal Lake keys; 2,760 scheduled modules;
four affected tools; current crate keys; 52 trust audits /
1,571 roots. All 1,541 old axiom sets and 29 old public
headers in changed files are exact. Ownership covers
3,747 standard-only core / 893 fixed witness constants,
172 core / 28 witness / 18 executable owners and
31 exact fixed native facts (previous 29 + 2). One bundled domain review reports
only the three standard axioms and no source warnings.

Real regalloc2 and Lean allocation retain complete-attempt retry and missing
oracle controls. All 24 objects pass 2,256 native comparisons with zero
failures/disagreements. Every vector and expected result of all eight previous
classes is exact. Zero and all-ones inputs exercise popcount. Current popcount
and retained bit-operation actual CLI/link/generated cohorts each pass 32 checks,
including 33-function slices, retained reconstruction, stack bounds and both
preparation modes. Original flat-multiply inputs/ELF/proof sources stay byte-exact;
fresh current proofs compile in both modes.

The attached JSON records corpus/encoder results, both E2E identity reports and
all original 1,150 / prior 1,159 identities and ordered stages, verified fv-demo
and survey results, exact source heads, input keys, logs and output hashes.

## Provenance, resources and remaining scope

The early alternate helper/RHS drafts and failed builds remain archived. Two 8 GiB build scopes
OOMed on existing arithmetic dependencies; a subsequent 16 GiB build succeeded.
The alternate guarded-frame lemma was isolated to avoid that dependency fan-out.
A draft interface-preservation mistake was corrected before author validation:
old theorem variants remain byte-exact, and alternatives are backed separately. Parse errors
in consumer/witness drafts were corrected before the frozen checks. The first native
checker stopped at an incomplete expected-name list before byte execution; its
failed record is retained. The harness fix passed a preflight and then all gates
were rerun on the final source commit. Failures
never count as passing validation. Independent integration cohorts use separate
one-gate manifests within the shared resource budget.

Terminal evidence is remotely verified at `6e9e92da938cf056332b203599dbb823030b9191` on
`agent/stock-popcnt-evidence-20261022T013714Z`; archive SHA256 `a36c370c4ddad32ecf0e5e246dc6cb8419f1a56051a7f5b67448aaf1011b7fd7`,
16,782,198 bytes / 1,583 files. Canonical recovery source
remains untouched. Four necessary views, one physical warm cache, over 700 GiB
free and max 16 GiB aggregate / two jobs. Expendable generated outputs are
archived before removal; no other projects are cleaned.

Full original #140 remains unfinished. Successful Stock lowering is still a
source-refinement premise; universal request/lowering and downstream completeness
remain obligations. Fallback is not Stock completeness. Next are comparisons /
min/max, high multiplication, division/remainder, complete original integer
widths/ABIs and all remaining original control, memory, traps, effects, calls,
source/block/whole-driver simulation, completeness and consumer obligations.

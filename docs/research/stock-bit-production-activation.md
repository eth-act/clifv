# Stock unary bit operations and rotations in production

Validated source ab08eefa050c867a41a94410c6a638d04a81915f, based on main `f74880a6`.
The shared default scalar route now supports negation, CLZ, CTZ, bit reversal,
byte swap, and left/right rotations for i32/i64. Original input conditions,
old theorem variants/selectors, exact required axiom sets, accepted identities
and ordered successful stages remain. The cleanup whitelist is unchanged.

## Proof and production boundary

The class reuses saved instruction-derived dispatch and source transfers from
StockUnaryDispatch, StockCountSourceValues and StockRotateSourceValues.
Retained results, demanded/available values and original-source execution
compose record/body/entry-return/no-trap proofs into the existing Scalar.Domain.
Additional cast variants take the exact source-format exclusions required by
the proof; every old CastBody.Family variant retains its original header.
The extended source family derives those exclusions internally.

The same compiler/checker/linker/generated-proof consumers are used. Pure BitRR
and register/immediate EXTR producers extend ABI framing, transport and machine
realization without changing earlier constant/shift/extension selectors.
The complete witness selects all nine intended new roots per configuration:
756 (negation), 922/927 (counts), 918 (bit reversal), 933/934 (byte swap),
901/902 and 903/904 (register/immediate ROTL), 907/908 and 910/911 (ROTR).
Its six ABIs and both cleanup modes retain arbitrary inputs and the original
arbitrary explicit slot, all prior scalar computation, shared/dead work, a ninth
stack argument, and opposite-width immediate rotation counts. Only two new
fixed native facts enter witnesses; universal compiler proofs stay standard-only.

## Validation

All 18 primary gates and 17 ownership partitions passed on frozen source:
2,752 normal Lake keys (2,749 scheduled modules),
four tools and 1,579 crate keys; 51 trust audits / 1,541 roots;
all 1,506 prior axiom sets and 45 old public headers exact. Ownership covers
3,093 standard-only core / 849 fixed witness constants,
156 core / 27 witness / 16 executable owners and 29 exact fixed native facts
(previous 27 + 2). One bundled domain review reports only the three standard
axioms and no source warnings.

Both real regalloc2 and Lean allocation retain whole-attempt retry and missing
oracle controls. All 24 objects pass 2,064 native comparisons / 516 Cranelift
reference executions with zero failures/disagreements. Every previous native
vector/expectation is unchanged; a new vector makes CTZ(0) observable in return.
Current bit and retained cast actual CLI/link/generated cohorts each pass 32
checks, including 33-function slices, retained reconstruction, stack bounds and
both preparation modes. Original flat-multiply inputs/ELF/proof sources stay
byte-exact; fresh current proofs compile in both modes.

Corpus: 4,737 passed / 0 failed, with the same 7 known non-runnable cases.
Encoder: 1,321 identical / 0 different. Both E2E modes accept 1,159 / reject 0,
retaining original 1,150 and prior 1,159 identities and ordered stages exactly.
Verified fv-demo passes 21 tests / 2 binaries; survey passes 53 tests / 18 binaries.
JSON retains every source head, input key, log and individual output hash.

## Provenance, resources and remaining scope

An audit-script path was caught outside the library target before scheduling;
that failed pre-gate record is retained, and its audit remains in the trust gate.
A missing prior-family import was fixed during composition. Prototype parse/root
errors are retained; failures never count as passing validation.
Independent current and retained integration cohorts use separate one-gate
manifests and the two available slots after other gates release capacity.

Terminal evidence is remotely verified at 9f4c6d0ed389e6f5c2738a27e54d6f259d2ef232 on
agent/stock-bit-evidence-20261021T234755Z; archive SHA256 03be53bd0f5497df9d329cb7e6ff69172b75300ce6a38116dc2f7e89fde514ca,
11,198,080 bytes / 1,026 files. Canonical recovery
source remains untouched. Four necessary views, one physical warm cache,
740 GiB free and max 16 GiB aggregate / two jobs. Expendable generated outputs
are archived before removal; no other projects are cleaned.

Full original #140 remains unfinished. Successful Stock lowering remains a
source-refinement premise; fallback is not Stock-only completeness. Popcount,
comparisons/min/max, high multiply, division/remainder, complete original integer
widths/ABIs, control, memory/traps/effects/calls and whole-driver simulation /
completeness / consumers remain. Existing popcount numerical/vector-helper
proofs and scoped projection should be reused for the next concrete packet.

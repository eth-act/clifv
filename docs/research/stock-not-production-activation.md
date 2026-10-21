# Stock NOT production activation

Extend the existing scalar production class with ordinary i32/i64 NOT. The
original source opcode and actual first-match selection derive all three roots:
plain NOT, shifted NOT and NOT-of-XOR. Existing result binding and guarded source
proofs feed scan/body/entry/return/no-trap composition and the shared Scalar.Domain.
The default compiler, checker, Lean linker and generated proofs use their existing
consumers. No consumer or ABI/model/allocator implementation changes in this packet.

Validated source and terminal backup are recorded in the
[gate/provenance receipt](stock-not-production-activation.json), based on
`150738a95f619380001100ca791fd3cdcb233cdc` (#361).
Terminal evidence is remotely verified at `817b6526d81197b4f833779c2e37ab074e343993`,
archive SHA256 `aacfea291c75a3ec2ed51a6c98fa2088a4358198c65f69fc5be7d487d5645112`.
The receipt checks 17 primary command gates and eight ownership partitions.
Shift-containing whole functions await the shift class; general selected-root
and guarded source proofs already cover shifted NOT.

The old constant classifier and theorem are unchanged; a separate extended
classifier derives the new source family. Every previous theorem variant and
original availability, scope, dominance, memory/world and ABI condition remains.
No selected root, runtime proof object or source restriction is added to callers.

All 2,694 current normal library keys, affected tools and 1,579 crate-proof keys
pass. All 47 trust audits pass, covering 1,399 distinct roots. All 1,378 previous
axiom sets and three old classifier theorem headers are exact. Eight ownership
partitions cover 2,632 standard-only core constants and 673 fixed-witness constants
across 114 core, 23 witness and seven executable owners. Exactly 21 declared native
facts are permitted: the previous 19 plus two fixed NOT pipeline/source facts.
One bundled domain review passes Std3 without warnings.

The complete witness spans six ABIs and both cleanup modes, arbitrary original
arguments and explicit slot address, a real stack argument, constants, NOT-of-XOR,
logical look-through, old pure families and dead producers. Strict real-regalloc2
and missing-oracle controls pass. Native execution checks 24 actual encoded objects
with 1,176 comparisons against 294 Cranelift executions: no failures/disagreements.
The native reference binary hash is unchanged.

Current NOT and retained-scalar actual CLI/link/generated-proof cohorts each pass
32 subchecks, including both cleanup modes, retained routes, 33-function slices,
actual ELF bytes and four emitted CLI proofs. Runtime/native grids include every
previous production class, including the newly retained constant class. Existing
consumers and all older fixture sources are byte-identical to #361. Historical
standalone helper evidence stays historical; affected corpus/encoder/E2E/examples
run fresh. Corpus: 4,737 pass, zero failures/disagreements, the same seven known
non-runnable cases. Encoding: 1,321 identical functions, zero differences. Both
E2E modes preserve all original 1,150 and previous 1,159 identities and ordered
successful stages. Verified fv-demo matches LLVM on 21 tests and both binaries;
survey matches on 53 tests and all 18 binaries.

Evidence retains its actual source provenance. The only later source delta after
`1372d0ae` corrects the native test's expected function inventory. The completed
NOT integration helper passed all 32 checks with its frozen FV/FVTest sources,
script and tools. Its outer runner correctly rejected a changed whole-checkout
fingerprint during that independent native-test fix. Explicit input-equivalence
verification checks every source/tool/log hash and return code; it preserves the
failed outer record and the actual completed inner receipt. No integration input
or semantic gate was waived. Current keys and retained-scalar integration pass
at the final source head. Initial fixture return-index, reporting-label and native
inventory failures remain preserved, not counted as passes.

An inherited test-manifest export path briefly reused the earlier scalar artifact
directory. All 72 NOT inputs/objects/tables were preserved separately; 194 original
scalar files were restored byte-for-byte from its remotely backed archive before
native checking. The recovery receipt and both failed and successful evidence are
included in the terminal backup. Sources and earlier evidence are preserved.

This completes another production class, with original #140 still open. Next are
multiplication/fused multiply, shifts/casts and remaining scalar families, control,
memory/traps/effects, calls/exceptions, full source/block/whole-driver simulation,
Stock-only success/completeness and remaining consumers. Fallback is not Stock
completeness. Multiplication dispatch and guarded source-transfer drafts already
build and are backed with this packet; continue the execution plan and ledger.

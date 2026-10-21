# Stock constant production activation and shared scalar consumers

Enable ordinary single-block i32/i64 constant/add/sub/select/AND/OR/XOR functions
through the default compiler, checker, Lean linker and generated proofs. Original
scope, dominance, ABI, parameter and return conditions remain. Every old entry
point and theorem variant remains available.

Validated source: `edfe4f4f13c65dd965a435f46bda63619965f065`, based on
`22a05d3b94f9874ba4f408a7338c07d57fa12a0a` (#360).
[Terminal provenance and gate receipt](stock-scalar-production-activation.json).

A fixed source-check soundness proof constructs `Stock.Scalar.Domain`, carrying
universal source-return and trap refinement under the original memory/world and
ABI relations. Existing consumers use this common boundary; subsequent scalar
families extend its proof without a new compiler/checker/linker stack. Shared
pure source execution, entry/return and ABI transport/realization composition
retain all old statements. No runtime proof object or selected-root certificate
is required. Multi-word constants have MOVK step proofs through a separate scalar
ABI read boundary; the old ABI checker and cleanup whitelist stay unchanged.

The complete retry order is Scalar → Logical → Mixed → Arithmetic → legacy,
with the original source and settings on every attempt. Artifact reconstruction
probes each direct route against actual bytes and records its index. Tests cover
retained intermediate routes and the original legacy bytes rather than assuming
that a name-based skip chooses the right implementation.

All 2,683 normal library keys, affected tools and 1,579 crate-proof keys pass.
All 46 checked-in trust audits pass, covering 1,378 distinct roots. The 1,329
previous axiom sets and 50 old public theorem headers remain exact, including
ABI declarations moved into the shared step module. Ownership scans cover 2,588
standard-only core constants and 634 fixed-witness constants across 106 core and
22 witness owners. Exactly 19 declared native facts are allowed: the previous
17 plus two fixed scalar pipeline/source witnesses. Executable owners pass
separately. One bundled MCP review passes Std3 without warnings.

Complete witnesses cover all six ABIs and both cleanup modes, nine parameters,
an actual stack argument, an explicit slot, multi-word/shared constants, every
retained pure family and dead producers. Strict real-regalloc2 settings and a
missing-oracle negative control pass. Native execution checks 24 actual encoded
objects with 1,008 comparisons against 252 Cranelift reference executions,
without failures or disagreements. The reference binary hash remains unchanged.

Scalar and retained logical/mixed actual CLI/link/generated-proof cohorts pass
in both cleanup modes, including 33-function slices. All older D0, prologue,
all-ABI, scalar-add and arithmetic runtime/oracle/link/generated/default CLI
checks pass; the old scalar-add test files remain byte-identical to #360.
Corpus runtime passes 4,737 cases with no failures/disagreements and the same
seven known non-runnable cases. Encoding matches all 1,321 functions. Both E2E
modes preserve every original 1,150 and previous 1,159 identity and ordered
successful stage. Verified fv-demo matches LLVM on 21 tests and both binaries;
survey matches on 53 tests and all 18 binaries.

Core/native evidence retains its actual `93146669` provenance. The only later
changes repair two tests: an old negative-control constant is now correctly
promoted, and retained-proof assertions inspect actual non-default scalar route
indices. Current normal keys, the affected ownership scan and all integration
checks pass at the final source head; unchanged core/native inputs are explicitly
verified. Parser, initial ABI-check and earlier fixture/assertion failures are
preserved and never counted as passes. Terminal unique evidence is backed
remotely at `fe81690da74d73eaf9985992d1e2e35a13f6620d`, archive SHA256
`c40570c3f5bcb088e9ec531250383126f4309c0485edbc6a93f3a28618380583`.
The receipt verifies 35 primary command gates and seven ownership records (six
initial partitions and the affected final-head replay).

This is another complete production class within #140. NOT/fused and remaining
scalar families, control/memory/calls/effects, original/synthetic/block/whole-driver
simulation, Stock-only success/completeness and remaining consumers stay open.
Fallback is not Stock completeness. Continue with the execution plan and obligation
ledger; historical inventory counts are not semantic coverage percentages.

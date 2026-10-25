# Original-block source and machine body composition

This packet removes the single-block restriction from the shared Stock
scalar/division/bmask/nop body contracts. It is a prerequisite for CFG production
activation; it does not activate branches, loops, effects or calls.

`StockQuietSourceRecords` derives quiet metadata, unsunkness and source records
for arbitrary original blocks. `StockMaskBlockRecords` classifies their actual
records, including colored division and zero-result nop. `StockMaskBlockRefines`
reuses the existing record semantics to compose returning and trapping bodies.
Actual executable source runs supply the source steps internally.

The new `actual_local_source_trap_or_continue` retains arbitrary terminators and
caller stacks. A trap in a later block yields a normally executed current body
and a trapping source continuation. It cannot be misclassified as a trap in the
current body. The old return-only trap theorem and all single-block variants
remain unchanged.

`StockQuietBlockWitness` and `StockMaskBlockWitness` use an actual two-block Stock
run: the entry block contains an unused constant and nop, passes two successor
arguments, and the successor divides and applies bmask. Real ABI worlds inhabit
the machine entry guards. Executable source witnesses cover both a zero-divisor
trap in the successor and successful return with divisor one. The six new
general body/record/source roots use only standard axioms. Fixed witnesses reuse
the compiler-run native fact and add a fixed input-dominance native fact; neither
is a premise or dependency of the general results.

Validation in progress: targeted normal build and the 15-root body audit pass;
one bundled MCP review reports precisely the standard axioms plus those two
fixed witness facts, with no source-scan warnings. Full FV/FVTest normal keys and
the complete repository axiom audit are required before landing. The preceding
quiet-source packet has its own 10-root audit and bundled MCP receipt.

Next: compose successor entry and branch execution with these body contracts,
retain real per-successor edge arguments through preparation/allocation and the
production consumers, and cover critical edges and loops. Reuse the existing
Stock preparation totality/checker completeness proofs. Memory/effects,
calls/unwind, general source/whole-driver simulation, original-domain and
downstream completeness, and all original #140 obligations remain open.

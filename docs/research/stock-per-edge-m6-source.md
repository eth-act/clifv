# Indexed M6 simulation and concrete function-entry witnesses

The full M6 register-allocation proof now has separate per-successor variants in
`FV/Backend/Proof/PerEdgeRegallocSound.lean`. Accepted `checkAllocAt` allocations
simulate `VStepAt` over the supplied actual outgoing vectors. The port reuses
the existing instruction, dead-definition, concrete-store and parallel-copy
lemmas. Actual branch successor indices feed the indexed verifier/edge proof.
All old checker, semantic and theorem variants remain unchanged.

The 19 new public proof roots cover checked/certificate extraction, entry,
forward simulation, progress, complete executions, returns and callee-saved
parts, halts, stuckness and divergence. Five public witness roots in four
modules inhabit these interfaces using complete actual Stock.lower runs:

- Three-block original-scope/dominated conditional, allocated at x0: concrete
  csem executes Args, the selected conditional edge and the return from function
  entry for every Arm world and every initial virtual register file. The same
  allocation is rejected by the old checker because its outgoing arguments
  cannot be represented by the old single-vector contract.
- The same complete conditional explicitly inhabits checked-state entry, the
  forward-step/progress wrappers and allocation-certificate simulation. A
  nonsemantic move arm after Args is excluded using the checked next index.
- Original Stock trap: actual source trap, complete concrete csem machine halt
  and corresponding virtual halt from function entry.
- Original-scope/dominated Stock caller: execute Args and prove the actual call
  is stuck when the concrete external-call semantics supplies no result. The
  full prefix and universal absence of outgoing steps are proved, rather than
  assumed.
- Original-scope/dominated two-block Stock loop: construct a concrete infinite
  machine trace from function entry, then derive VCode runs of every length.

Closed observations of complete Stock lowering and allocations use normal
kernel decisions; the only diagnostic native evaluation inspected call operand
shape and is not used as proof evidence. Computable Except equality instances
are file-local. A bundled MCP run audits all 24 new roots once; no repeated
lean_verify calls. The normal full audit compares all 1,677 previous recorded
axiom sets, including the seven compiler sets, exactly.

This is full indexed M6 simulation, not full source/Stock-driver correctness or
a production cutover. Production still uses the legacy driver. Preparation,
return/source composition, machine instruction/bytes consumers, spill fallback,
compiler, linker and generated-proof consumers still require indexed migration.
In particular, the real allocation path currently serializes only VCode and its
single branchArgs vector; its spill fallback also copies only that vector.
Removing StockComparison/StockTest's rejection before migrating BOTH request
serialization and checked fallback would lose accepted edge semantics. Preserve
actual raw Stock order, numbering and outgoing vectors; do not add input filters
or insert edge blocks merely to fit the old model.

Next: transport vectors through prepare's reachability filtering, critical-edge
splitting and reverse-postorder renumbering (or prove a Stock-specific no-change
case internally), serialize actual indexed vectors to regalloc2, validate returned allocations with
checkAllocAt, and implement/prove an indexed fallback with real selected copies.
Then migrate StockComparison/StockTest and their concrete regression witnesses.
Continue general actual Stock CFG/label/target proofs, branch/source/DFG/world
composition, all remaining rule/effect/trap/sinking obligations, whole-driver
simulation/completeness, production consumers and the fresh full Stock comparison
under the original accepted inputs and all original parity/#179 gates.

Machine-readable evidence and the complete full-goal checklist are maintained in
`stock-per-edge-m6-checkpoint.json`; gate finalization records exact results.

Batch gates pass: full2369/crates1171/runtime4672/0/0 (same7/families), encoder1292identical0different, both E2E1150accepted0rejected; baseline identity/stage bytes unchanged. Normal1701-root audit preserves all1677 prior/seven compiler sets;24 new standard-only sets match one bundled MCP. No production cutover or final Stock comparison claimed.

# Actual fused binary logical-NOT values

Part of #140, following squash-merged #179 (cc29aaa). Branch
agent/stock-logic-not-values-pr; reuse the existing warm driver worktree.

1. Reuse the proven commutative-helper request/match receipts: Lean MCP verified
   RHS and matching-field equality for3939/3916,3941/3920,3944/3928, and full
   positive-fuel match execution equality. Add thin actual NOT-helper receipts
   rather than rebuilding those proofs. Reuse aluVal_holds_not/NotOp, landed
   register/immediate/LSL helpers and current demand/alias invariants.
2. Prove all three actual term566 helper selections establish notOpVal through
   final aliases, then original-source value for the six mirrored AND/OR/XOR
   roots and bnot(bxor). Reuse existing bnot_value/instData inversion and generic
   record binding; retain baseline restricted DFG and demand/availability guards.
3. Inhabit complete selected record/source runs, audit via Lean MCP/kernel,
   run required gates with exact baseline E2E identity/stage parity, and publish
   one combined helper/root/record/source batch with a compact incremental audit.

No production behavior or legacy T6/IselLcf/Cov/optimizer edits. Other semantic
families/effects, whole simulation/completeness and actual production cutover
remain under #140. Helper receipt implementation starts locally; no PR yet.

Local checkpoint: StockLogicalNotReceipts reuses five exact RHS/match contracts.
StockLogicalNotSemantics proves mapped/final-alias register/immediate/LSL NOT
machine values. StockLogicalNotValues composes every successful actual term566
selection into notOpVal with fresh-only writes and actual demanded coverage.
StockLogicalNotWitness executes allnine operation/form cases in the shared sparse
fixtures, with constants/shifts unmaterialized in machine registers. Normal
capped witness build passes363 jobs; all files have clean Lean MCP diagnostics.
StockLogicalNotLookthrough reuses existing instData_bnot_inv/bnot_value to derive
real source definitions and complement values from an actual nested NOT pattern.

Step2 root/record/source integration and Step3 complete-root/source witnesses and
full repository gates remain before publication. No new PR or production change.

Recovery checkpoint 2026-10-13: the seven local modules now include
StockLogicalNotRootValues and StockLogicalNotMatch. Actual successful matching
derives the canonical environment and hidden NOT source; selected-root values
for all six mirrored roots compile. Fresh normal capped Match+Witness build
passes368 jobs and all17 public roots use only standard axioms. The seventh
bnot(bxor) fusion, retained record/source composition, complete witnesses and
full batch gates remain. Resume from
[the recovery plan](test-binary-alignment-recovery.md), which records the saved
dirty-file backup and distinguishes landed validation from local progress.

## Validated continuation batch

All seven fused roots, actual retained-record/binding and guarded source transfer
are now proved. Complete record/source-step witnesses cover six mirrored roots
and NOT-of-XOR at32/64, plus unmaterialized constant/shift selections at32/64.
All13 modules build. All30 public roots pass fresh Lean MCP and normal transitive
axiom audits with only standard3; all226 prior sets and final compiler sets stay
unchanged. Full1484/crates1171/runtime4672/0fail/0disagree with7known non-runnable,
encoder1292identical/0different and bothE2E1150accepted/0rejected pass. Every E2E
identity and successful stage equals #179 and both modes agree.

Evidence: [incremental audit](../research/stock-logical-not-values-audit.json).
Work is local; no push or merge. Production remains legacy. Continue with
[remaining families](stock-driver-remaining-families.md); #140 stays incomplete.

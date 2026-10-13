# Actual scalar bnot values and source transfer

Part of #140, following squash-merged #178 (cd324c7). Branch
agent/stock-bnot-values-pr; worktree ~/clifv/.worktrees/driver-proof-resume.

1. Reuse stock_alu_rrr_helper and the existing legacy orr_not_run,
   ispec_xzr_orrNot, not_shl_fin and ispec_orn_shift_fb results. Derive real
   Stock request/state/RHS observations for scalar bnot base and LSL forms;
   reuse current mapped bounds, source look-through and final-alias machinery.
2. Establish original unary values and fresh-only machine preservation, then
   connect actual selected roots and singleton result binding to retained
   records. Retain baseline restricted-frame DFG and demand/availability guards.
3. Inhabit real base and fused-shift executions plus source transfer; verify
   through Lean MCP and normal trust audits. Run required repository gates,
   compare all baseline E2E identities/stages and publish one combined PR.

No compiler behavior, shared T6/IselLcf/Cov or optimizer changes. Reuse existing
proofs rather than replacing their interfaces. Fused binary logical-not roots,
other semantic families/effects, whole simulation/completeness and production
integration remain under #140. Implementation complete locally: StockBnotRhs, StockBnotSemantics,
StockBnotMatch, StockBnotValues, StockBnotRecordValues and StockBnotWitness.
All base/fused-shift record and actual source-step witnesses at32/64 bits pass
Lean MCP/kernel checking. Original source/DFG facts derive valid shift amount,
typed environment and unchanged matching state; successful RHS derives its safe
request and full marking/allocation/emission state. Whole-run receipts derive
binding, mapped bounds and final-alias size. Source transfer retains the original
restricted-frame DFG and demand/availability guards.

Shared existing shift-pattern value extraction is exposed for both binary and
unary matching. Existing demand-preserving binding is exposed and its duplicate
private proof removed from StockLogicalRecordValues. No legacy proof interface
or compiler behavior changes. All gates pass: full1471/crates1171, runtime4672/0/0 with seven unchanged
not-runnable cases, encoder1292/0, E2E1150/0 with all identity/stage fields
equal to #178. All210 prior trust sets unchanged; 16 new public roots standard-only
in normal226-root audit and batched MCP check. Compact receipt:
docs/research/stock-bnot-values-audit.json. Ready for one combined PR.

Keep publication frequency reduced: one review-ready batch, minimal pushes,
compact incremental audit receipt referencing #178's prior root inventory.

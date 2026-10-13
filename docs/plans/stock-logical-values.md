# All selected logical helper value cases

Part of #140, following merged #176; fresh-main branch
agent/stock-logical-values-pr.

1. Reuse actual helper rule inversion and the matching/RHS/source-value receipts
   to compose register, both immediate sides and both nested-shift sides.
2. Derive demanded operand coverage from actual marked output state and mapped
   source bounds. Prove emitted instruction, original binary value and preservation
   of every register except the fresh destination under final alias resolution.
3. Inhabit actual helper executions for all five forms using mapped contexts,
   consistent restricted source frames and held inputs; audit via Lean MCP/kernel.
4. Connect to actual selected logical roots and records, deriving bounds and
   retaining original source-step/value-transfer and availability conditions.
5. Run repository gates before publication. Production switch follows whole
   simulation/completeness and remaining instruction-family/effect proofs.

Steps1–3 compile in StockLogicalValues. Actual ORR64 executions inhabit every
selected helper form in real sparse-ID contexts and DFG-consistent frames;
constant and shift definitions not demanded by the helper remain unmaterialized
in the machine register file. Each selected rule ID is kernel checked. Step4
remains. Caller
composition uses LowerSim.Match's DFGCons ctx (restrict frame available) and
holds demanded values in that restricted frame, preserving the baseline
availability guard rather than requiring future/stale values in full frames.
Mapped bounds are supplied by the already-proven actual record demand extent.
Other families/effects and the production cutover remain under #140.

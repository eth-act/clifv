# Actual logical RHS observations

Part of #140, following merged #175; fresh-main branch
agent/stock-logical-observed-pr.

1. Reuse successful scalar request inversion to derive safe mapped operands from
   successful immediate/shift RHS execution, covering both commutative sides.
2. Compare with existing forward RHS execution to derive output register and the
   complete marked/fresh/emitted Stock state; no caller request/code certificates.
3. Inhabit all four forms at32/64 bits and verify with Lean MCP/kernel audits.
4. Compose five helper cases with matching/source-value receipts and mapped
   execution semantics, then complete record/source-step value transfer.
5. Run repository gates before publication; preserve existing compiler contracts.

Register/immediate/shift observations and all corresponding32/64-bit witnesses
compile in StockLogicalObserved. Step4 remains. Use the existing restricted source
frame: LowerSim.Match carries DFGCons ctx (restrict frame available), so a successful
getAs on that frame supplies availability. Keep demanded-and-available coverage;
demand alone can include future or stale definitions. Other semantic families/effects, whole simulation/completeness and
production cutover remain under #140.

# Actual logical helper execution

Part of #140, following #173; fresh-main branch agent/stock-logical-helper-pr.

1. Reuse generic RHS/output inversion to extract the actual term565 logical
   helper call from selected logical-root RHS execution.
2. Evaluate the root's actual typed arguments, preserve the exact Stock
   intermediate state and trace, and inhabit the bridge using the complete
   AND/OR/XOR selected-record witnesses from #173.
3. Invert the actual helper case and compose mapped source/machine values for
   all five forms: registers, immediate on either side, shift on either side.
4. Validate with Lean MCP, cumulative trust audit and repository gates before
   publication; preserve old interfaces and production behavior.

Steps1–2 compile in StockLogicalHelper. The mapped, alias-resolved immediate/LSL
machine execution and fresh-write frame facts compile in StockLogicalSemantics,
with actual RHS3920/3928 emission-to-execution witnesses at32/64 bits for all three
logical operations. Step3 still needs selected-case inversion, original DFG
look-through value facts and the complete record/source-step composition. Other semantic families,
reserved writes/memory/traps/deferred sinking, whole simulation/completeness and
production cutover remain under #140.

# Logical look-through values from actual matches

Part of #140, following merged #174; fresh-main branch
agent/stock-logical-lookthrough-pr.

1. Transport actual Stock source patterns through the existing pure matcher
   projection and proof-only identity-register context view.
2. From successful immediate matches on either side, derive the real constant
   definition and use original DFG consistency to establish its held source value.
   Inhabit both sides with a genuine sparse-ID context and consistent frame.
3. Derive analogous nested shift/constant source definitions and values; connect
   actual matching to valid immediate/shift operands and typed environments.
4. Compose these derived facts with actual helper execution and mapped machine
   value lemmas, then whole-record/source-step value transfer for all five forms.
5. Run Lean MCP, cumulative trust audits and repository gates before publication.

Steps1–3 compile in StockLogicalLookthrough. Immediate and nested LSL matching
receipts now derive their typed environments, complete unchanged state, valid
operands/source values and shift bounds. Both operand sides are inhabited with
genuine sparse-ID contexts and consistent frames. Step4 remains. No production
behavior change. Remaining families/effects, whole simulation/completeness and
production cutover remain under #140.

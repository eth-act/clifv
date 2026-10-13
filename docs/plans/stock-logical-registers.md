# Actual logical register helper

Part of #140. Reuse StockAlu's proved pure interpreter projection to expose the
shared alu_rrr helper for arbitrary supported operation tags. Reuse actual scalar
request contracts to prove logical RHS3916 marks both operands, returns its fresh
register and emits the corresponding mapped instruction. Inhabit AND/OR/XOR at
32/64 bits and connect existing alias-resolved machine value semantics. Preserve
old interfaces/runtime; normal/MCP audits and required gates precede publication.

This is the register case needed by bitwise root coverage. Immediate and shifted
logical helpers, actual root selection composition, other families/effects,
whole simulation/completeness and production switch remain.

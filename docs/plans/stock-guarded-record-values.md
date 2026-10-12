# Guarded actual-record value transfer

Part of #140, following merged final-alias bridge #162.

1. Restore the saved family-independent guarded value transfer. Use actual
   single-result binding/final resolution and source-available register exclusion
   from whole-driver proofs. Keep before/after availability guards and allow the
   required demand set to change.
2. Relate a successful single-result source instruction to the source-frame
   update used by value transfer, including removal of the source statement.
3. Inhabit the complete execution bridge with actual sparse-ID add lowering:
   parameters7/31 hold7/5, stale source result100 holds99, and emitted ADD195
   produces12. Observe actual allocation interval195..196, operand demand marking,
   source maps and retained emitted result. The actual source step and machine
   execution establish the newly available demanded result and preserve arguments.
4. Validate normal/MCP axiom sets, full/crate/runtime/encoder/E2E gates and exact
   baseline identity/stage parity; publish a bounded PR.

Remaining internal family obligations: derive execution, fresh-def bounds and
demand monotonicity for all selected rule shapes. This bridge does not add source
restrictions or a program certificate. Successful selection/safety, other families,
reserved writes, memory/traps/deferred sinking, complete block/function simulation
and completeness remain before production cutover. Compiler behavior unchanged.

# Shared fresh-result record bridge

Part of #140, following merged add/subtract contracts #161.

1. Extract actual emission and output results from a retained emitted scan.
2. Use actual virtual binding and SSA record-to-final preservation to derive the
   installed final alias for any single fresh virtual source result. Reuse the
   actual whole-run resolver theorem; require no family alias certificate.
3. Inhabit the bridge with complete Stock add lowering: sparse result100 maps194,
   the actual retained ADD writes195, and its final alias resolves194 to195.
4. Validate normal/MCP audits, full/crate/runtime/encoder/E2E gates and unchanged
   baseline identities; publish this reusable bridge.

Next: the guarded family-independent value transfer already typechecked locally
in the development checkpoint. Its complete execution witness and ALU integration
remain; development text is preserved at /tmp/stock-fresh-record-values-guard.lean
on this machine. It is not part of this published alias bridge or a new accepted
program certificate. Connect family execution/def/demand contracts to actual
source steps, then cover remaining shapes/families/reserved writes/memory/traps,
full simulation/completeness and production cutover. Compiler behavior unchanged.

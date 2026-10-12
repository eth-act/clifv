# Actual selected ALU record value transfer

Part of #140, based on merged request inversion #165.

1. Connect successful add/subtract RHS and named-root receipts to actual emitted
   records and virtual-result binding. Derive the single instruction, fresh output
   and allocation endpoints instead of supplying code/definition certificates.
2. Compose alias-resolved ALU execution and the availability-guarded whole-record
   transfer. Derive final destination resolution and machine definition bounds
   from actual whole-driver records; retain source-step memory transport.
3. Inhabit the contracts with complete Stock add and subtract functions using
   sparse source IDs, preserving both arguments and replacing a stale result.
4. Run normal/MCP trust audits, full/crate/runtime/encoder/E2E gates and exact
   identity/stage parity; publish a bounded PR.

Typed selected-RHS/named-root receipts and source operand values still need to
be derived uniformly from actual selection and the simulation invariant. This
slice does not establish selection coverage or whole-driver completeness. Other
families, reserved writes, memory/traps/deferred sinking, block/function
composition and the production switch remain. Compiler behavior is unchanged.

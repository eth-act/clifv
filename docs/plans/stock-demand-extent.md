# Actual demand-array extent

Prerequisite for docs/plans/stock-operand-coverage.md and #140, based on merged
actual ALU record transfer #166 (057dc00).

Prove size preservation for every successful actual constructor, nested/named
interpreter run, result binding and scan decision. Carry it through successor
argument collection, branch emission, block cores and actual reverse node
traversal, including every stored record. Context construction and the actual
source register map then derive input/output demand bounds for every mapped
source value, including sparse source IDs. Inhabit all contracts with nonempty
marking/helper/named calls, a real scan and a complete sparse-ID add record.

Validate normal/MCP trust audits, full/crate/runtime/encoder/E2E gates and exact
baseline identity/stage parity; publish this independent prerequisite. No compiler
behavior or existing public statement changes.

Next: source dominance plus actual requested demand coverage yields the separate
ALU operand-value premise from the guarded invariant. Uniform selected-root
receipts, other families, reserved writes, memory/traps/deferred sinking, whole
simulation/completeness and the production switch remain.

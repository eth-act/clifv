# Derive actual ALU operand coverage

Part of #140, following selected actual record transfer #166.

1. Prove successful scalar/vector constructors and nested/named evaluation preserve
   demand-array size. Reuse constructor/binding/scan preservation proofs.
2. Carry this through branches, outgoing arguments, block cores and actual node
   traversal to every retained record. Context construction supplies the initial
   extent and register-map bounds.
3. Derive source operand availability from unchanged dominance/source context.
   The actual marked output demands then put both add/subtract operands in the
   guarded invariant. Keep the old transfer and add a variant deriving its
   separate operand-value premise.
4. Update real add/subtract source-step witnesses to use automatic coverage;
   audit normal/MCP trust, required gates and baseline identities; bounded PR.

Uniform selected-root receipts, other families, reserved writes, memory/traps,
full simulation/completeness and production cutover remain. No runtime changes.

Checkpoint: constructor/interpreter/scan and whole-record extent plus mapped
source demand bounds are implemented in StockDemandExtent. Steps 1–2 are the
independent prerequisite; source-availability/guarded-coverage integration and
updated automatic ALU transfer remain under steps 3–4.

Integration checkpoint: StockAluOperandCoverage derives generic source operand
availability from the retained original DFG and unchanged dominance. Actual
add/subtract marked demands plus whole-run map bounds put both operands in the
guarded invariant. The original transfer remains available; the automatic variant
uses only that invariant. Existing complete add/subtract source-step fixtures are
reused with the automatic variant. No runtime/default/source-scope changes.

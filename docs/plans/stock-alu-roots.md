# Stock register-register ALU roots

Part of #140, following merged actual constant-record/source transfer #160.

1. Reuse the existing pure width/output/add/subtract helpers and shared ALU
   machine semantics. Prove constructor-closed transport for their reachable
   terms; preserve Stock scheduling fields through those pure helper calls.
2. Prove the actual Stock add/subtract root match and RHS execution. Its revised
   operand constructors mark both source values and retain their dense mapped
   registers. Preserve all original Isel theorem statements and runtime code.
3. Reuse the shared add/subtract/and/or/xor semantic template through the actual
   finite-fuel alias resolver. Establish the new result and preservation of every
   other register, without identifying source IDs with virtual register numbers.
4. Inhabit matching, demand marking, execution and semantics using actual context
   construction with sparse source IDs7/31/100, mapped192/193/194, and fresh195.
   Exercise both add/subtract and32/64-bit instruction sizes.
5. Validate normal full/crate builds, runtime/encoder/E2E gates, unchanged
   identities and normal/MCP axiom sets; publish a bounded PR.

Remaining: connect these selected-rule contracts to actual retained records and
availability-guarded source-step transfer, deriving operand safety/demand premises
from successful selection. Named-entry selection and other rule shapes/families,
reserved writes, memory/traps/deferred sinking, whole simulation/completeness and
the production cutover remain. Compiler behavior and accepted scope are unchanged.

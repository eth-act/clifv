# Logical immediate and shifted-register helpers

Part of #140, following logical register helper #171.

1. Reuse interpreter projection and frame preservation to prove Stock helpers
   `alu_rr_imm_logic` (360) and `alu_rrr_shift` (377).
2. Prove actual RHS3920/3923/3928/3931, accounting for mapped operand requests,
   demand marking, fresh allocation, emitted instructions and complete Stock state.
3. Inhabit both helpers and all four RHS cases at 32 and 64 bits.
4. Audit the seven public roots with Lean MCP and the normal kernel audit; preserve
   all earlier roots and final compiler theorem axiom sets. Run repository gates.

Steps 1–3 are implemented in `StockLogicalForms.lean`. This slice proves helper
execution and emission, without a compiler behavior change. The witness uses
ORR, immediate255 and LSL3; the helper/RHS theorems are generic in the operation.

Next: compose actual logical helper/root selection with source values and existing
machine semantics. Other families/effects, reserved writes, memory/traps/deferred
sinking, whole simulation/completeness and production cutover remain under #140.

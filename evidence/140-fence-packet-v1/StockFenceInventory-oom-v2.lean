import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The original source opcode admits exactly the actual fence root. -/
theorem stock_fence_opcode_inventory : sourceOpcodeIds 160 = [1024] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

end Backend.Stock.Proof

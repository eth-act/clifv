import FV.Backend.Proof.IselData
import FV.Arm.BitVec
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof
set_option maxRecDepth 20000
/-- Kernel algebra for the narrow opposite count; unlike the legacy fact this
proof has no bit-blasting dependency. -/
theorem stock_small_rotate_neg {w : Nat} (width : w = 8 ∨ w = 16)
    (b : BitVec 32) (bounded : b.toNat < w) :
    (0 - (b - BitVec.ofNat 32 w)).toNat = w - b.toNat := by
  have algebra : 0 - (b - BitVec.ofNat 32 w) = BitVec.ofNat 32 w - b := by
    exact (BitVec.zero_sub _).trans (by
      rw [BitVec.neg_sub,BitVec.sub_eq_add_neg,BitVec.add_comm])
  rw [algebra,BitVec.toNat_sub,BitVec.toNat_ofNat]
  rcases width with rfl | rfl <;> simp <;> omega
end Backend.Stock.Proof.ScalarRotate

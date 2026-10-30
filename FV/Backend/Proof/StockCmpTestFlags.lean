import FV.Backend.Proof.IselSemCmp
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend
/-- Kernel-checked truth of the exact masked flag test used by8-bit comparisons. -/
theorem stock_cmp_test255_truth (a : BitVec 32) :
    condOn Cond.ne.bits (andsFlags (a &&& BitVec.ofNat 32 255)) = (a.setWidth 8 != 0) := by
  have zero : (a &&& BitVec.ofNat 32 255 = 0) ↔ a.setWidth 8 = 0 := by
    rw [BitVec.toNat_eq,BitVec.toNat_eq]
    simp only [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.zero_mod]
    rw [show 255 % 2^32 = 2^8-1 from by decide +kernel,Nat.and_two_pow_sub_one_eq_mod]
    rfl
  have normalized : condOn Cond.ne.bits (andsFlags (a &&& BitVec.ofNat 32 255)) =
      !(decide (a &&& BitVec.ofNat 32 255 = 0)) := by
    simp [condOn,Cond.bits,andsFlags,Arm.make_pstate]
    rfl
  rw [normalized]
  apply Bool.eq_iff_iff.mpr
  simp [bne,beq_iff_eq,zero]
  exact not_congr zero
/-- Original8-bit values establish masked-test truth without legacy native lemmas. -/
theorem stock_cmp_truthy8 (b : BitVec 8) (a : CV) (held : VHolds ⟨.i8,b⟩ a) :
    condOn Cond.ne.bits (andsFlags (opnd .size32 a &&& BitVec.ofNat OperandSize.size32.bits 255)) =
      Clif.Sem.truthy b := by
  show condOn Cond.ne.bits (andsFlags (((lo64 a).setWidth 32 : BitVec 32) &&& BitVec.ofNat 32 255)) = _
  rw [stock_cmp_test255_truth]
  simp only [VHolds,Clif.Ty.width] at held
  simp only [Clif.Sem.truthy,←held,lo64]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_setWidth_of_le _ (by decide)]
end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.StockCmpFlags
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.PrepareCheck
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem right_extension {n : Nat} (width : n = 8 ∨ n = 16) (signed : Bool) (B : CV) :
    Arm.extend_reg (opnd .size32 B)
      (Arm.decode_reg_extend (if signed then (if n = 8 then ExtendOp.sxtb else .sxth)
        else (if n = 8 then ExtendOp.uxtb else .uxth)).bits) 0 =
      (if signed then (B.setWidth n).signExtend 32 else (B.setWidth n).setWidth 32) := by
  have low (k : Nat) (hk : k ≤ 32) : (opnd .size32 B).extractLsb' 0 k = B.setWidth k := by
    change ((B.setWidth 64).setWidth 32).extractLsb' 0 k = B.setWidth k
    rw [← BitVec.setWidth_eq_extractLsb' hk]
    change ((B.setWidth 64).setWidth 32).setWidth k = B.setWidth k
    rw [BitVec.setWidth_setWidth_of_le _ hk,BitVec.setWidth_setWidth_of_le _ (by omega)]
  rcases width with rfl | rfl <;> cases signed
  · change ((opnd .size32 B).extractLsb' 0 8).setWidth 32 <<< 0 = _
    rw [BitVec.shiftLeft_zero,low 8 (by decide)]
    rfl
  · change ((opnd .size32 B).extractLsb' 0 8).signExtend 32 <<< 0 = _
    rw [BitVec.shiftLeft_zero,low 8 (by decide)]
    rfl
  · change ((opnd .size32 B).extractLsb' 0 16).setWidth 32 <<< 0 = _
    rw [BitVec.shiftLeft_zero,low 16 (by decide)]
    rfl
  · change ((opnd .size32 B).extractLsb' 0 16).signExtend 32 <<< 0 = _
    rw [BitVec.shiftLeft_zero,low 16 (by decide)]
    rfl
/-- The actual narrow extended-register comparison computes the original
predicate from an explicitly extended left operand and the original right low
bits. No native fixed-width arithmetic proof is used. -/
theorem stock_cmp_narrow_extended_flags {n : Nat} (width : n = 8 ∨ n = 16)
    (cc : Clif.IntCC) {a b : BitVec n} {A B : CV}
    (left : DivOpnd (signedCC cc) a A) (right : B.setWidth n = b) :
    condOn (condOf cc).bits (cmpFlags (opnd .size32 A)
      (Arm.extend_reg (opnd .size32 B)
        (Arm.decode_reg_extend (if signedCC cc then (if n = 8 then ExtendOp.sxtb else .sxth)
          else (if n = 8 then ExtendOp.uxtb else .uxth)).bits) 0)) = Clif.Sem.intcc cc a b := by
  have small : n ≤ 32 := by rcases width with rfl | rfl <;> decide
  unfold DivOpnd at left
  simp only [small,ite_true] at left
  change opnd .size32 A = (if signedCC cc then a.signExtend 32 else a.setWidth 32) at left
  rw [right_extension width,right,left]
  change condOn (condOf cc).bits (cmpFlags (if signedCC cc then a.signExtend 32 else a.setWidth 32)
    (if signedCC cc then b.signExtend 32 else b.setWidth 32)) = Clif.Sem.intcc cc a b
  rw [stock_cmp_conditions (n := 32) (Or.inl rfl)]
  cases signed : signedCC cc <;> simp only [signed,Bool.false_eq_true,ite_false,ite_true]
  · exact stock_cmp_unsigned_extension small cc signed a b
  · exact stock_cmp_signed_extension small cc signed a b
/-- Both signednesses, both widths and the signed minimum versus minus-one
boundary inhabit the original-operand extended comparison contract. -/
theorem stock_cmp_narrow_extended_flags_witness (cc : Clif.IntCC) (n : Nat) (width : n = 8 ∨ n = 16) :
    ∃ A B : CV,DivOpnd (signedCC cc) (BitVec.intMin n) A ∧ B.setWidth n = (-1 : BitVec n) ∧
      condOn (condOf cc).bits (cmpFlags (opnd .size32 A)
        (Arm.extend_reg (opnd .size32 B)
          (Arm.decode_reg_extend (if signedCC cc then (if n = 8 then ExtendOp.sxtb else .sxth)
            else (if n = 8 then ExtendOp.uxtb else .uxth)).bits) 0)) =
        Clif.Sem.intcc cc (BitVec.intMin n) (-1 : BitVec n) := by
  let A : CV := ofX (if signedCC cc then (BitVec.intMin n).signExtend 64 else (BitVec.intMin n).setWidth 64)
  let B : CV := -1
  have left : DivOpnd (signedCC cc) (BitVec.intMin n) A := by
    unfold DivOpnd
    cases cc <;> rcases width with rfl | rfl <;> decide +kernel
  have right : B.setWidth n = (-1 : BitVec n) := by rcases width with rfl | rfl <;> decide +kernel
  exact ⟨A,B,left,right,stock_cmp_narrow_extended_flags width cc left right⟩
end Backend.Stock.Proof.ScalarCmp

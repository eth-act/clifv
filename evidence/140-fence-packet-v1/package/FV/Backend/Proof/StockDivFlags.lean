import FV.Backend.Proof.IselSemCmp
import FV.Backend.Proof.DriverCheck
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Kernel arithmetic for the divisor-minus-one test. This new variant leaves
all legacy fixed-width theorem variants and their trust sets untouched. -/
theorem stock_div_condOn_adds1 {n : Nat} (a : BitVec n) :
    condOn Cond.eq.bits (Arm.AddWithCarry a (BitVec.ofNat n 1) 0#1).2 =
      (a == BitVec.allOnes n) := by
  have zero : a + BitVec.ofNat n 1 = 0 ↔ a = BitVec.allOnes n := by
    rw [← BitVec.eq_sub_iff_add_eq]
    change a = 0#n - 1#n ↔ a = BitVec.allOnes n
    rw [BitVec.zero_sub,BitVec.neg_one_eq_allOnes]
  have normalized : condOn Cond.eq.bits (Arm.AddWithCarry a (BitVec.ofNat n 1) 0#1).2 =
      decide ((Arm.AddWithCarry a (BitVec.ofNat n 1) 0#1).1 = 0) := by
    simp [condOn,Cond.bits,Arm.AddWithCarry,Arm.make_pstate]
  rw [normalized,Arm.fst_AddWithCarry_eq_add]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,beq_iff_eq] using zero
private theorem extended_sub_one {n : Nat} (width : n = 32 ∨ n = 64) (a : BitVec n) :
    (a.signExtend (n+1) - 1).toInt = a.toInt - 1 := by
  have low := BitVec.toInt_intMin_le a
  have high := BitVec.toInt_lt (x := a)
  have positive : 0 < n := by omega
  rw [BitVec.toInt_intMin_of_pos positive] at low
  rw [BitVec.toInt_sub,BitVec.toInt_signExtend_of_le (by omega)]
  have one : (1 : BitVec (n+1)).toInt = 1 := by rcases width with rfl | rfl <;> rfl
  rw [one]
  apply Int.bmod_eq_of_le
  all_goals rcases width with rfl | rfl <;> omega

/-- Subtracting one commutes with one-bit signed extension exactly when the
original operand is not its signed minimum. Ordinary integer bounds prove it. -/
theorem stock_div_extension_sub_one {n : Nat} (width : n = 32 ∨ n = 64) (a : BitVec n) :
    (a - 1).signExtend (n+1) = a.signExtend (n+1) - 1 ↔ a ≠ BitVec.intMin n := by
  have low := BitVec.toInt_intMin_le a
  have high := BitVec.toInt_lt (x := a)
  have positive : 0 < n := by omega
  have minimum := BitVec.toInt_intMin_of_pos positive
  rw [minimum] at low
  rw [← BitVec.toInt_inj,BitVec.toInt_signExtend_of_le (by omega),BitVec.toInt_sub,
    extended_sub_one width a]
  have one : (1 : BitVec n).toInt = 1 := by rcases width with rfl | rfl <;> rfl
  rw [one,Int.bmod_eq_iff (show 0 < 2^n by exact Nat.two_pow_pos n)]
  have distinct : a ≠ BitVec.intMin n ↔ a.toInt ≠ -2^(n-1) := by
    simp only [ne_eq,← BitVec.toInt_inj,minimum]
  rw [distinct]
  rcases width with rfl | rfl <;> simp only [Int.sub_self,Int.dvd_zero,and_true] <;> omega
/-- The actual subtract-one overflow flag is true exactly at signed minimum;
this proof uses ordinary integer bounds, leaving legacy variants unchanged. -/
theorem stock_div_condOn_sub1_vs {n : Nat} (width : n = 32 ∨ n = 64) (a : BitVec n) :
    condOn Cond.vs.bits (cmpFlags a (BitVec.ofNat n 1)) = (a == BitVec.intMin n) := by
  have result : (Arm.AddWithCarry a (~~~(BitVec.ofNat n 1)) 1#1).1 = a - 1 := by
    rw [Arm.fst_AddWithCarry_eq_sub_neg,BitVec.not_not]
    rfl
  have constants : (~~~(BitVec.ofNat n 1)).signExtend (n+1) + (1#1).zeroExtend (n+1) =
      -(1 : BitVec (n+1)) := by rcases width with rfl | rfl <;> rfl
  have signed : a.signExtend (n+1) + (~~~(BitVec.ofNat n 1)).signExtend (n+1) +
      (1#1).zeroExtend (n+1) = a.signExtend (n+1) - 1 := by
    rw [BitVec.add_assoc,constants,BitVec.sub_eq_add_neg]
  have normalized : condOn Cond.vs.bits (cmpFlags a (BitVec.ofNat n 1)) =
      decide ((Arm.AddWithCarry a (~~~(BitVec.ofNat n 1)) 1#1).1.signExtend (n+1) ≠
        a.signExtend (n+1) + (~~~(BitVec.ofNat n 1)).signExtend (n+1) + (1#1).zeroExtend (n+1)) := by
    simp [condOn,Cond.bits,cmpFlags,Arm.AddWithCarry,Arm.make_pstate]
    decide
  rw [normalized,result,signed]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
  simpa only [ne_eq,Classical.not_not] using not_congr (stock_div_extension_sub_one width a)
end Backend.Stock.Proof.ScalarDiv

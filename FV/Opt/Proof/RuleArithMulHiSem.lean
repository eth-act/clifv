import FV.Opt.Proof.InterpEval

namespace Opt.Proof

open Clif

/-- Shifting a double-width word by one half leaves exactly its unsigned high half. -/
theorem mulhi_ushift_extract {w : Nat} (z : BitVec (w + w)) :
    z >>> w = (z.extractLsb' w w).zeroExtend (w + w) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases h : i < w
  · simp [BitVec.zeroExtend, hi, h]
  · simp [BitVec.zeroExtend, hi, h, BitVec.getLsbD_of_ge z (w + i) (by omega)]

/-- Arithmetic shifting fills the upper half with the sign of the extracted high half. -/
theorem mulhi_sshift_extract {w : Nat} (hw : 0 < w) (z : BitVec (w + w)) :
    z.sshiftRight w = (z.extractLsb' w w).signExtend (w + w) := by
  have hsign : (z.extractLsb' w w).msb = z.msb := by
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb']
    simp [show w - 1 < w by omega, show w + (w - 1) = w + w - 1 by omega]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases h : i < w
  · simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_extractLsb', hi, show ¬ w + w ≤ i by omega, h,
      show w + i < w + w by omega, decide_true, decide_false,
      Bool.not_false, Bool.true_and, ite_true]
  · simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
      hi, show ¬ w + w ≤ i by omega, h,
      show ¬ w + i < w + w by omega, decide_true, decide_false,
      Bool.not_false, Bool.true_and, ite_false, hsign]

/-- No multiplication expansion: instantiate the unsigned extraction identity at the product. -/
theorem mulhi_unsigned {w : Nat} (x y : BitVec w) :
    (Sem.uextend (w + w) x * Sem.uextend (w + w) y) >>> w =
      Sem.uextend (w + w) (Sem.umulhi x y) :=
  mulhi_ushift_extract _

/-- No multiplication expansion: instantiate the signed extraction identity at the product. -/
theorem mulhi_signed {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    (Sem.sextend (w + w) x * Sem.sextend (w + w) y).sshiftRight w =
      Sem.sextend (w + w) (Sem.smulhi x y) :=
  mulhi_sshift_extract hw _

-- Concrete instances witness every helper, including negative and high-bit inputs.
example : (0x8001#16) >>> 8 = ((0x8001#16).extractLsb' 8 8).zeroExtend 16 :=
  mulhi_ushift_extract _
example : 0 < (8 : Nat) ∧
    (0x8001#16).sshiftRight 8 = ((0x8001#16).extractLsb' 8 8).signExtend 16 :=
  ⟨by decide, mulhi_sshift_extract (w := 8) (by decide) _⟩
example : (Sem.uextend 128 (0xffffffffffffffff#64) *
    Sem.uextend 128 (0x8000000000000000#64)) >>> 64 =
      Sem.uextend 128 (Sem.umulhi (0xffffffffffffffff#64) (0x8000000000000000#64)) :=
  mulhi_unsigned _ _
example : 0 < (64 : Nat) ∧
    (Sem.sextend 128 (0x8000000000000000#64) *
      Sem.sextend 128 (0x7fffffffffffffff#64)).sshiftRight 64 =
        Sem.sextend 128 (Sem.smulhi (0x8000000000000000#64) (0x7fffffffffffffff#64)) :=
  ⟨by decide, mulhi_signed (w := 64) (by decide) _ _⟩

end Opt.Proof

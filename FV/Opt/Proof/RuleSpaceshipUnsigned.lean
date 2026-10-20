import FV.Clif.Sem
import Lean.Elab.Tactic.Omega

/-!
Unsigned select forms of the spaceship operator from `spaceship.isle`.
The comparison width and result width are independent, including zero-width and
truncating results. Only the two `ineg` forms require an eight-bit result.
-/

namespace Opt.Proof

open Clif

/-- The prelude's unsigned spaceship expansion, whose result is always i8. -/
def spaceship_u_bits {w : Nat} (x y : BitVec w) : BitVec 8 :=
  Sem.icmp .ugt x y - Sem.icmp .ult x y

private theorem spaceship_u_sextend_neg (v : Nat) :
    Sem.sextend v (255#8) = BitVec.ofInt v (-1) := by
  rfl

private theorem spaceship_u_sextend_zero (v : Nat) :
    Sem.sextend v (0#8) = 0#v := by
  rfl

private theorem spaceship_u_sextend_one (v : Nat) :
    Sem.sextend v (1#8) = 1#v := by
  rfl

/-- Unsigned trichotomy fixes all six comparison values before extending results. -/
private theorem spaceship_u_order_cases {w : Nat} (x y : BitVec w) :
    (Sem.icmp .ult x y = 1#8 ∧ Sem.icmp .ugt x y = 0#8 ∧
      Sem.icmp .eq x y = 0#8 ∧ Sem.icmp .ne x y = 1#8 ∧
      Sem.icmp .ule x y = 1#8 ∧ Sem.icmp .uge x y = 0#8) ∨
    (Sem.icmp .ult x y = 0#8 ∧ Sem.icmp .ugt x y = 0#8 ∧
      Sem.icmp .eq x y = 1#8 ∧ Sem.icmp .ne x y = 0#8 ∧
      Sem.icmp .ule x y = 1#8 ∧ Sem.icmp .uge x y = 1#8) ∨
    (Sem.icmp .ult x y = 0#8 ∧ Sem.icmp .ugt x y = 1#8 ∧
      Sem.icmp .eq x y = 0#8 ∧ Sem.icmp .ne x y = 1#8 ∧
      Sem.icmp .ule x y = 0#8 ∧ Sem.icmp .uge x y = 1#8) := by
  rcases Nat.lt_trichotomy x.toNat y.toNat with hlt | heq | hgt
  · left
    have hne : x ≠ y := by
      intro h
      subst y
      omega
    have hnotgt : ¬ y.toNat < x.toNat := by omega
    have hle : x.toNat ≤ y.toNat := by omega
    have hnotge : ¬ y.toNat ≤ x.toNat := by omega
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.ult, BitVec.ule,
      hlt, hne, hnotgt, hle, hnotge]
  · right; left
    have hxy : x = y := BitVec.eq_of_toNat_eq heq
    subst y
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.ult, BitVec.ule]
  · right; right
    have hne : x ≠ y := by
      intro h
      subst y
      omega
    have hnotlt : ¬ x.toNat < y.toNat := by omega
    have hnotle : ¬ x.toNat ≤ y.toNat := by omega
    have hge : y.toNat ≤ x.toNat := by omega
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.ult, BitVec.ule,
      hgt, hne, hnotlt, hnotle, hge]

local macro "spaceship_unsigned_order " x:ident y:ident : tactic => `(tactic| (
  rcases spaceship_u_order_cases $x $y with h | h | h
  all_goals
    rcases h with ⟨hlt, hgt, heq, hne, hle, hge⟩
    simp (config := { decide := true }) [spaceship_u_bits, hlt, hgt, heq, hne, hle, hge,
      Sem.select, Sem.truthy, Sem.bmask, Sem.uextend,
      spaceship_u_sextend_neg, spaceship_u_sextend_zero, spaceship_u_sextend_one,
      BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 8)]))

/-- `x < y ? -1 : uextend(x != y)`. -/
theorem spaceship_select_13 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ult x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .ne x y)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x < y ? -1 : uextend(x > y)`. -/
theorem spaceship_select_19 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ult x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .ugt x y)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x == y ? 0 : (x < y ? -1 : 1)`. -/
theorem spaceship_select_25 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .ult x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x == y ? 0 : (x <= y ? -1 : 1)`. -/
theorem spaceship_select_32 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .ule x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x == y ? 0 : (x > y ? 1 : -1)`. -/
theorem spaceship_select_39 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .ugt x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x == y ? 0 : (x >= y ? 1 : -1)`. -/
theorem spaceship_select_46 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .uge x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x > y ? 1 : -(x < y)`, necessarily at the comparison-result width. -/
theorem spaceship_select_55 {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ugt x y) (1#8) (-(Sem.icmp .ult x y)) =
    spaceship_u_bits x y := by
  spaceship_unsigned_order x y

/-- `x > y ? 1 : bmask(x < y)`. -/
theorem spaceship_select_59 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ugt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .ult x y)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-- `x > y ? 1 : -(x != y)`, necessarily at the comparison-result width. -/
theorem spaceship_select_65 {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ugt x y) (1#8) (-(Sem.icmp .ne x y)) =
    spaceship_u_bits x y := by
  spaceship_unsigned_order x y

/-- `x > y ? 1 : bmask(x != y)`. -/
theorem spaceship_select_69 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .ugt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .ne x y)) =
    Sem.sextend outWidth (spaceship_u_bits x y) := by
  spaceship_unsigned_order x y

/-! Each source pattern has less/equal/greater witnesses. Unsigned extrema and
the 127/128 high-bit boundary distinguish unsigned from signed ordering. -/

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ult x y) (BitVec.ofInt n (-1))
        (Sem.uextend n (Sem.icmp .ne x y))
    lhs 8 0#8 255#8 = 255#8 ∧
      lhs 1 128#8 128#8 = 0#1 ∧ lhs 128 128#8 127#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_13] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ult x y) (BitVec.ofInt n (-1))
        (Sem.uextend n (Sem.icmp .ugt x y))
    lhs 8 127#8 128#8 = 255#8 ∧
      lhs 1 255#8 255#8 = 0#1 ∧ lhs 128 255#8 0#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_19] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .eq x y) (0#n)
        (Sem.select (Sem.icmp .ult x y) (BitVec.ofInt n (-1)) (1#n))
    lhs 8 0#8 255#8 = 255#8 ∧
      lhs 1 128#8 128#8 = 0#1 ∧ lhs 128 128#8 127#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_25] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .eq x y) (0#n)
        (Sem.select (Sem.icmp .ule x y) (BitVec.ofInt n (-1)) (1#n))
    lhs 8 127#8 128#8 = 255#8 ∧
      lhs 1 255#8 255#8 = 0#1 ∧ lhs 128 255#8 0#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_32] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .eq x y) (0#n)
        (Sem.select (Sem.icmp .ugt x y) (1#n) (BitVec.ofInt n (-1)))
    lhs 8 0#8 255#8 = 255#8 ∧
      lhs 1 128#8 128#8 = 0#1 ∧ lhs 128 128#8 127#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_39] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .eq x y) (0#n)
        (Sem.select (Sem.icmp .uge x y) (1#n) (BitVec.ofInt n (-1)))
    lhs 8 127#8 128#8 = 255#8 ∧
      lhs 1 255#8 255#8 = 0#1 ∧ lhs 128 255#8 0#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_46] <;> decide

example :
    let lhs := fun (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ugt x y) (1#8) (-(Sem.icmp .ult x y))
    lhs 0#8 255#8 = 255#8 ∧ lhs 128#8 128#8 = 0#8 ∧
      lhs 128#8 127#8 = 1#8 := by
  dsimp only
  simp only [spaceship_select_55] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ugt x y) (1#n)
        (Sem.bmask (w := n) (Sem.icmp .ult x y))
    lhs 8 127#8 128#8 = 255#8 ∧
      lhs 1 255#8 255#8 = 0#1 ∧ lhs 128 255#8 0#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_59] <;> decide

example :
    let lhs := fun (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ugt x y) (1#8) (-(Sem.icmp .ne x y))
    lhs 127#8 128#8 = 255#8 ∧ lhs 255#8 255#8 = 0#8 ∧
      lhs 255#8 0#8 = 1#8 := by
  dsimp only
  simp only [spaceship_select_65] <;> decide

example :
    let lhs := fun n (x y : BitVec 8) =>
      Sem.select (Sem.icmp .ugt x y) (1#n)
        (Sem.bmask (w := n) (Sem.icmp .ne x y))
    lhs 8 0#8 255#8 = 255#8 ∧
      lhs 1 128#8 128#8 = 0#1 ∧ lhs 128 128#8 127#8 = 1#128 := by
  dsimp only
  simp only [spaceship_select_69] <;> decide

/-! Zero-width input and output, one-bit truncation, and result widths on both
sides of i8. These are not additional premises on any identity above. -/

example :
    Sem.select (Sem.icmp .ult (0#0) (0#0)) (BitVec.ofInt 129 (-1))
      (Sem.uextend 129 (Sem.icmp .ne (0#0) (0#0))) = 0#129 := by
  rw [spaceship_select_13] <;> decide

example :
    let lhs := fun n =>
      Sem.select (Sem.icmp .ult (0#1) (1#1)) (BitVec.ofInt n (-1))
        (Sem.uextend n (Sem.icmp .ugt (0#1) (1#1)))
    lhs 0 = 0#0 ∧ lhs 1 = 1#1 ∧ lhs 7 = 127#7 ∧ lhs 9 = 511#9 := by
  dsimp only
  simp only [spaceship_select_19] <;> decide

end Opt.Proof

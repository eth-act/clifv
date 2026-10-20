import FV.Clif.Sem

/-!
# Signed spaceship select identities

These are the width-parametric value identities for the ten signed select roots in
`opts/spaceship.isle`. The comparison result is always i8, as in
`prelude_opt.isle:74`; only the surrounding result is extended. In particular, the
`ineg` alternatives at lines 120 and 130 force the select itself to have width 8.
-/

namespace Opt.Proof

open Clif

/-- The exact i8 expansion of `spaceship_s` in the pinned prelude. -/
def spaceship_s_bits {w : Nat} (x y : BitVec w) : BitVec 8 :=
  Sem.icmp .sgt x y - Sem.icmp .slt x y

private theorem spaceship_s_sextend_neg (v : Nat) :
    Sem.sextend v (255#8) = BitVec.ofInt v (-1) := by
  rfl

private theorem spaceship_s_sextend_zero (v : Nat) :
    Sem.sextend v (0#8) = 0#v := by
  rfl

private theorem spaceship_s_sextend_one (v : Nat) :
    Sem.sextend v (1#8) = 1#v := by
  rfl

/-- Integer trichotomy gives all six comparison values without bit blasting. -/
private theorem spaceship_s_order_cases {w : Nat} (x y : BitVec w) :
    (Sem.icmp .slt x y = 1#8 ∧ Sem.icmp .sgt x y = 0#8 ∧
      Sem.icmp .eq x y = 0#8 ∧ Sem.icmp .ne x y = 1#8 ∧
      Sem.icmp .sle x y = 1#8 ∧ Sem.icmp .sge x y = 0#8) ∨
    (Sem.icmp .slt x y = 0#8 ∧ Sem.icmp .sgt x y = 0#8 ∧
      Sem.icmp .eq x y = 1#8 ∧ Sem.icmp .ne x y = 0#8 ∧
      Sem.icmp .sle x y = 1#8 ∧ Sem.icmp .sge x y = 1#8) ∨
    (Sem.icmp .slt x y = 0#8 ∧ Sem.icmp .sgt x y = 1#8 ∧
      Sem.icmp .eq x y = 0#8 ∧ Sem.icmp .ne x y = 1#8 ∧
      Sem.icmp .sle x y = 0#8 ∧ Sem.icmp .sge x y = 1#8) := by
  rcases Int.lt_trichotomy x.toInt y.toInt with hlt | heq | hgt
  · left
    have hne : x ≠ y := by
      intro h
      subst y
      omega
    have hnotgt : ¬ y.toInt < x.toInt := by omega
    have hle : x.toInt ≤ y.toInt := by omega
    have hnotge : ¬ y.toInt ≤ x.toInt := by omega
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.slt, BitVec.sle,
      hlt, hne, hnotgt, hle, hnotge]
  · right; left
    have hxy : x = y := BitVec.toInt_inj.mp heq
    subst y
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.slt, BitVec.sle]
  · right; right
    have hne : x ≠ y := by
      intro h
      subst y
      omega
    have hnotlt : ¬ x.toInt < y.toInt := by omega
    have hnotle : ¬ x.toInt ≤ y.toInt := by omega
    have hge : y.toInt ≤ x.toInt := by omega
    simp [Sem.icmp, Sem.intcc, Sem.bool8, BitVec.slt, BitVec.sle,
      hgt, hne, hnotlt, hnotle, hge]

local macro "spaceship_signed_cases" x:ident y:ident : tactic => `(tactic| (
  rcases spaceship_s_order_cases $x $y with h | h | h
  all_goals
    rcases h with ⟨hlt, hgt, heq, hne, hle, hge⟩
    simp (config := { decide := true }) [spaceship_s_bits, hlt, hgt, heq, hne, hle, hge,
      Sem.select, Sem.truthy, Sem.ineg, Sem.bmask, Sem.uextend,
      spaceship_s_sextend_neg, spaceship_s_sextend_zero, spaceship_s_sextend_one,
      BitVec.ofInt_neg, BitVec.neg_one_eq_allOnes,
      BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 8)]))

/-- `spaceship.isle:78`: the non-less branch is the extended inequality. -/
theorem spaceship_select_78 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .ne x y)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:84`: the non-less branch is the extended greater comparison. -/
theorem spaceship_select_84 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .sgt x y)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:90`: equality outside a strict less comparison. -/
theorem spaceship_select_90 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:97`: equality outside a non-strict less comparison. -/
theorem spaceship_select_97 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sle x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:104`: equality outside a strict greater comparison. -/
theorem spaceship_select_104 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sgt x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:111`: equality outside a non-strict greater comparison. -/
theorem spaceship_select_111 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sge x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:120`: negating the i8 comparison fixes the result width at 8. -/
theorem spaceship_select_120 {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .sgt x y) (1#8) (Sem.ineg (Sem.icmp .slt x y)) =
    spaceship_s_bits x y := by
  spaceship_signed_cases x y

/-- `spaceship.isle:124`: the less comparison supplies a result-width mask. -/
theorem spaceship_select_124 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .sgt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .slt x y)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-- `spaceship.isle:130`: negating the i8 inequality fixes the result width at 8. -/
theorem spaceship_select_130 {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .sgt x y) (1#8) (Sem.ineg (Sem.icmp .ne x y)) =
    spaceship_s_bits x y := by
  spaceship_signed_cases x y

/-- `spaceship.isle:134`: inequality supplies a result-width mask. -/
theorem spaceship_select_134 (outWidth : Nat) {w : Nat} (x y : BitVec w) :
    Sem.select (Sem.icmp .sgt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .ne x y)) =
    Sem.sextend outWidth (spaceship_s_bits x y) := by
  spaceship_signed_cases x y

/-! Each concrete witness checks every source LHS against an explicit signed result.
The matrix covers less/equal/greater, signed extrema, all CLIF widths, and the zero-
and one-bit boundaries admitted by the unconditional semantic statements. -/

private def spaceship_s_witness (outWidth : Nat) {w : Nat}
    (x y : BitVec w) (expected : Int) : Prop :=
  Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .ne x y)) = BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1))
      (Sem.uextend outWidth (Sem.icmp .sgt x y)) = BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .slt x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
      BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sle x y) (BitVec.ofInt outWidth (-1)) (1#outWidth)) =
      BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sgt x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
      BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .eq x y) (0#outWidth)
      (Sem.select (Sem.icmp .sge x y) (1#outWidth) (BitVec.ofInt outWidth (-1))) =
      BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .sgt x y) (1#8) (Sem.ineg (Sem.icmp .slt x y)) =
      BitVec.ofInt 8 expected ∧
  Sem.select (Sem.icmp .sgt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .slt x y)) = BitVec.ofInt outWidth expected ∧
  Sem.select (Sem.icmp .sgt x y) (1#8) (Sem.ineg (Sem.icmp .ne x y)) =
      BitVec.ofInt 8 expected ∧
  Sem.select (Sem.icmp .sgt x y) (1#outWidth)
      (Sem.bmask (w := outWidth) (Sem.icmp .ne x y)) = BitVec.ofInt outWidth expected

local macro "spaceship_signed_witness" : tactic => `(tactic| (
  simp only [spaceship_s_witness, spaceship_select_78, spaceship_select_84,
    spaceship_select_90, spaceship_select_97, spaceship_select_104, spaceship_select_111,
    spaceship_select_120, spaceship_select_124, spaceship_select_130, spaceship_select_134]
  decide))

example : spaceship_s_witness 0 (0#0) (0#0) 0 := by spaceship_signed_witness
example : spaceship_s_witness 1 (1#1) (0#1) (-1) := by spaceship_signed_witness
example : spaceship_s_witness 1 (1#1) (1#1) 0 := by spaceship_signed_witness
example : spaceship_s_witness 1 (0#1) (1#1) 1 := by spaceship_signed_witness

example : spaceship_s_witness 8 (BitVec.intMin 8) (BitVec.intMax 8) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 8 (BitVec.intMin 8) (BitVec.intMin 8) 0 := by
  spaceship_signed_witness
example : spaceship_s_witness 8 (BitVec.intMax 8) (BitVec.intMin 8) 1 := by
  spaceship_signed_witness

example : spaceship_s_witness 16 (BitVec.intMin 16) (BitVec.intMax 16) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 16 (BitVec.intMin 16) (BitVec.intMin 16) 0 := by
  spaceship_signed_witness
example : spaceship_s_witness 16 (BitVec.intMax 16) (BitVec.intMin 16) 1 := by
  spaceship_signed_witness

example : spaceship_s_witness 32 (BitVec.intMin 32) (BitVec.intMax 32) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 32 (BitVec.intMin 32) (BitVec.intMin 32) 0 := by
  spaceship_signed_witness
example : spaceship_s_witness 32 (BitVec.intMax 32) (BitVec.intMin 32) 1 := by
  spaceship_signed_witness

example : spaceship_s_witness 64 (BitVec.intMin 64) (BitVec.intMax 64) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 64 (BitVec.intMin 64) (BitVec.intMin 64) 0 := by
  spaceship_signed_witness
example : spaceship_s_witness 64 (BitVec.intMax 64) (BitVec.intMin 64) 1 := by
  spaceship_signed_witness

example : spaceship_s_witness 128 (BitVec.intMin 128) (BitVec.intMax 128) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 128 (BitVec.intMin 128) (BitVec.intMin 128) 0 := by
  spaceship_signed_witness
example : spaceship_s_witness 128 (BitVec.intMax 128) (BitVec.intMin 128) 1 := by
  spaceship_signed_witness

-- Cross-width cases distinguish sign extension from zero extension at the high bit.
example : spaceship_s_witness 128 (255#8) (0#8) (-1) := by spaceship_signed_witness
example : spaceship_s_witness 128 (0#8) (255#8) 1 := by spaceship_signed_witness
example : spaceship_s_witness 8 (BitVec.intMin 128) (0#128) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 0 (BitVec.intMin 128) (BitVec.intMax 128) (-1) := by
  spaceship_signed_witness
example : spaceship_s_witness 1 (BitVec.intMax 128) (BitVec.intMin 128) 1 := by
  spaceship_signed_witness

end Opt.Proof

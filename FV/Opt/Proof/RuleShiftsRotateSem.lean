import FV.Opt.Proof.InterpEval

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Clif
attribute [local implicit_reducible] Ty.width

/-- Every scalar data width divides the modulus of every scalar amount type,
including an i8 amount rotating an i128 value. -/
theorem rotate_width_dvd (t k : Ty) : t.width ∣ 2 ^ k.width := by
  cases t <;> cases k <;> decide

/-- Zero extension preserves the effective rotation amount; it need not reach
(or exceed) the data width. -/
theorem rotate_extend_amount (t : Ty) {u v : Nat} (x : BitVec u) (h : u ≤ v) :
    (x.setWidth v).toNat % t.width = x.toNat % t.width := by
  rw [BitVec.toNat_setWidth_of_le h]

/-- Wrapping addition of amounts agrees with addition modulo the data width. -/
theorem rotate_add_amount (t k : Ty) (a b : BitVec k.width) :
    (a + b).toNat % t.width = (a.toNat % t.width + b.toNat % t.width) % t.width := by
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (rotate_width_dvd t k), Nat.add_mod]

/-- Wrapping subtraction of amounts agrees with subtraction modulo the data
width, even on underflow and even when the amount type is narrower. -/
theorem rotate_sub_amount (t k : Ty) (a b : BitVec k.width) :
    (a - b).toNat % t.width =
      (t.width + a.toNat % t.width - b.toNat % t.width) % t.width := by
  have hb := b.isLt
  rw [BitVec.toNat_sub, Nat.mod_mod_of_dvd _ (rotate_width_dvd t k)]
  cases t <;> cases k <;> simp only [Ty.width, Nat.reducePow] at * <;> omega

-- These proofs reason about indices, not SAT circuits. Only the five data
-- widths are split; the amounts and the entire data word remain symbolic.
local macro "rotate_indices" : tactic => `(tactic| (
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  simp only [BitVec.getMsbD_rotateLeft, BitVec.getMsbD_rotateRight]
  repeat' split
  all_goals simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
  all_goals first | rfl | (congr 1 <;> omega)))

/-- Left/left composition at arbitrary (already reduced or unreduced) amounts. -/
theorem rotate_ll (t : Ty) (x : BitVec t.width) (a b c : Nat)
    (h : c % t.width = (a % t.width + b % t.width) % t.width) :
    (x.rotateLeft a).rotateLeft b = x.rotateLeft c := by
  cases t <;> simp only [Ty.width] at * <;> rotate_indices

/-- Right/right composition at arbitrary amounts. -/
theorem rotate_rr (t : Ty) (x : BitVec t.width) (a b c : Nat)
    (h : c % t.width = (a % t.width + b % t.width) % t.width) :
    (x.rotateRight a).rotateRight b = x.rotateRight c := by
  cases t <;> simp only [Ty.width] at * <;> rotate_indices

/-- Right after left subtracts the outer amount from the inner amount. -/
theorem rotate_lr (t : Ty) (x : BitVec t.width) (a b c : Nat)
    (h : c % t.width = (t.width + a % t.width - b % t.width) % t.width) :
    (x.rotateLeft a).rotateRight b = x.rotateLeft c := by
  cases t <;> simp only [Ty.width] at * <;> rotate_indices

/-- Left after right uses the same difference, in the right orientation. -/
theorem rotate_rl (t : Ty) (x : BitVec t.width) (a b c : Nat)
    (h : c % t.width = (t.width + a % t.width - b % t.width) % t.width) :
    (x.rotateRight a).rotateLeft b = x.rotateRight c := by
  cases t <;> simp only [Ty.width] at * <;> rotate_indices

-- Concrete witnesses cover all helper premises, both orientations, overflow,
-- underflow, high amount bits, data i128, and narrower/wider/equal amounts.
example : Ty.i128.width ∣ 2 ^ Ty.i8.width := by decide
example : (8 : Nat) ≤ 16 ∧
    ((255#8).setWidth 16).toNat % 128 = (255#8).toNat % 128 := by decide
example : ((255#8) + (3#8)).toNat % 128 = 2 ∧
    ((1#8) - (3#8)).toNat % 128 = 126 := by decide
example : (3 : Nat) % 128 = (129 % 128 + 130 % 128) % 128 ∧
    ((1#128).rotateLeft 129).rotateLeft 130 = (1#128).rotateLeft 3 ∧
    ((1#128).rotateRight 129).rotateRight 130 = (1#128).rotateRight 3 := by decide
example : (127 : Nat) % 128 = (128 + 129 % 128 - 130 % 128) % 128 ∧
    ((1#128).rotateLeft 129).rotateRight 130 = (1#128).rotateLeft 127 ∧
    ((1#128).rotateRight 129).rotateLeft 130 = (1#128).rotateRight 127 := by decide
example : ((1#128) + ((255#8).setWidth 128)).toNat % 128 = 0 ∧
    (((255#8).setWidth 128) - (256#128)).toNat % 128 = 127 ∧
    ((170141183460469231731687303715884105727#128) + (3#128)).toNat % 128 = 2 := by decide

end Opt.Proof

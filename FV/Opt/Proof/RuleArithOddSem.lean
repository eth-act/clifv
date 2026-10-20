import FV.Opt.Proof.RuleInfraDivConst
import Init.Data.Nat.Coprime

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- Odd multiplication is injective modulo every power of two. -/
theorem odd_mul_cancel {w : Nat} (c x y : BitVec w) (hc : c.toNat % 2 = 1) :
    x * c = y * c ↔ x = y := by
  constructor
  · intro h
    have hg : Nat.Coprime (2 ^ w) c.toNat := by
      apply Nat.gcd_pow_left_of_gcd_eq_one
      rw [Nat.gcd_rec, hc, Nat.gcd_one_left]
    have hz : c * (x - y) = 0#w := by
      rw [BitVec.mul_sub, BitVec.mul_comm c x, BitVec.mul_comm c y, h,
        BitVec.sub_self]
    have hd : 2 ^ w ∣ c.toNat * (x - y).toNat := by
      apply Nat.dvd_of_mod_eq_zero
      simpa only [BitVec.toNat_mul, BitVec.toNat_zero] using congrArg BitVec.toNat hz
    have hz' : (x - y).toNat = 0 := by
      have hm := Nat.mod_eq_zero_of_dvd (hg.dvd_of_dvd_mul_left hd)
      rw [Nat.mod_eq_of_lt (x - y).isLt] at hm
      exact hm
    have he : x - y = 0#w := BitVec.eq_of_toNat_eq (by simpa using hz')
    simpa using BitVec.sub_eq_iff_eq_add.mp he
  · rintro rfl
    rfl

/-- The exact unsigned helper quotient, converted by `imm64`, multiplies back
at every presented constant width. The width premise comes from presentation,
not from an additional guard on the original arithmetic rules. -/
theorem odd_quotient_product {w : Nat} (hw : w ≤ 64) (d c : BitVec w)
    (hr : (d.toNat : Int) % (c.toNat : Int) = 0) :
    BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int))) * c = d := by
  have hr' : d.toNat % c.toNat = 0 := by
    simpa only [← Int.natCast_emod, Int.natCast_eq_zero] using hr
  rw [DivConst.divc_ofInt_asI64 hw, ← Int.natCast_ediv, BitVec.ofInt_natCast]
  calc
    BitVec.ofNat w (d.toNat / c.toNat) * c =
        BitVec.ofNat w (d.toNat / c.toNat * c.toNat) := by
      rw [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    _ = d := by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr'), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]

/-- The equality used by all eight original odd-multiplier roots. -/
theorem odd_mul_quotient_beq {w : Nat} (hw : w ≤ 64) (d c x : BitVec w)
    (hr : (d.toNat : Int) % (c.toNat : Int) = 0)
    (hc : (c.toNat : Int) % 2 = 1) :
    (x * c == d) =
      (x == BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int)))) := by
  have hc' : c.toNat % 2 = 1 := by omega
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  calc
    x * c = d ↔ x * c =
        BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int))) * c := by
      rw [odd_quotient_product hw d c hr]
    _ ↔ _ := odd_mul_cancel c _ _ hc'

/-- The same exact quotient identity with the multiplication operands reversed. -/
theorem odd_mul_quotient_beq_left {w : Nat} (hw : w ≤ 64) (d c x : BitVec w)
    (hr : (d.toNat : Int) % (c.toNat : Int) = 0)
    (hc : (c.toNat : Int) % 2 = 1) :
    (c * x == d) =
      (x == BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int)))) := by
  rw [BitVec.mul_comm c x]
  exact odd_mul_quotient_beq hw d c x hr hc

/-- The same exact quotient identity with the comparison operands reversed. -/
theorem odd_mul_quotient_beq_rev {w : Nat} (hw : w ≤ 64) (d c x : BitVec w)
    (hr : (d.toNat : Int) % (c.toNat : Int) = 0)
    (hc : (c.toNat : Int) % 2 = 1) :
    (d == x * c) =
      (x == BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int)))) := by
  have hs : (d == x * c) = (x * c == d) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  rw [hs]
  exact odd_mul_quotient_beq hw d c x hr hc

/-- Both operand reversals used by the original generated rules. -/
theorem odd_mul_quotient_beq_left_rev {w : Nat} (hw : w ≤ 64) (d c x : BitVec w)
    (hr : (d.toNat : Int) % (c.toNat : Int) = 0)
    (hc : (c.toNat : Int) % 2 = 1) :
    (d == c * x) =
      (x == BitVec.ofInt w (Rust.asI64 ((d.toNat : Int) / (c.toNat : Int)))) := by
  have hs : (d == c * x) = (c * x == d) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact eq_comm
  rw [hs]
  exact odd_mul_quotient_beq_left hw d c x hr hc

-- Joint-premise witnesses: the multiplier is genuinely odd and nontrivial,
-- division is exact, and cancellation has both equal and unequal outcomes.
example : (3#8).toNat % 2 = 1 ∧
    (7#8) * (3#8) = 21#8 ∧ (8#8) * (3#8) = 24#8 := by decide
example : (8 : Nat) ≤ 64 ∧ (21 : Int) % 3 = 0 ∧
    BitVec.ofInt 8 (Rust.asI64 (21 / 3)) * (3#8) = 21#8 := by decide
example : (64 : Nat) ≤ 64 ∧
    (18446744073709551615 : Int) % 3 = 0 ∧ (3 : Int) % 2 = 1 ∧
    (6148914691236517205#64) * (3#64) = 18446744073709551615#64 ∧
    (6148914691236517206#64) * (3#64) ≠ 18446744073709551615#64 := by decide

end Opt.Proof

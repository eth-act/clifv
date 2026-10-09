import FV.Opt.Proof.RuleSkeleton3

/-!
# `simplify_skeleton` rules: signed division by a constant via magic numbers

`arithmetic.isle` 122, 125, 165, 168 replace `sdiv`/`srem` by a 32/64-bit constant whose absolute
value is not a power of two with Cranelift's signed `div_const` sequence
(`apply_div_const_magic_s32`/`_s64`, `prelude_opt.isle`): `q1 = smulhi x m`, the fix-up
`q2 = q1 + x` (`d > 0`, `m < 0`) / `q1 - x` (`d < 0`, `m > 0`) / `q1`, `q3 = q2 >>ₛ s`,
`qf = q3 + (q3 >>> (w - 1))`, and for `srem` `x - qf * d`. The magic numbers are
`DivConst.magicS_spec` (`FV/Opt/Proof/RuleInfraDivConst.lean`), wrapped as `sdc_magicS` for the
facts the rules check.

The template mirrors the unsigned one (`RuleSkeleton3`): the magic numbers are generalized, the
right-hand side is evaluated with their facts and the `iconst_s` range checks (`sdc_iconst_s32`/
`sdc_iconst_s64`), split per sign of the divisor and of the multiplier (which fix-up rule fires;
the evaluation prefix is shared, `sdc_eval`), and the bit-level goal is closed through `toInt`:
`sdc_smulhi_toInt` (floor of the double-width product), `BitVec.toInt_sshiftRight` (floor shift),
`sdc_sign_fix` (the sign correction), `BitVec.toInt_sdiv_of_ne_or_ne` (the divisor is not `-1`)
and `sdc_srem_of_sdiv`.

The divisor's `toInt` appears at two widths (`Ty.i64.width` from the matched immediate, `64` in
the magic numbers' argument); the facts about it are stated at both.
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-! ## Arithmetic -/

theorem sdc_two_pow_int (w : Nat) : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl

theorem sdc_two_pow_half {w : Nat} (hw : 1 ≤ w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  rw [show w = w - 1 + 1 by omega, Int.pow_succ]; simp; omega

theorem sdc_toInt_range {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    -2 ^ (w - 1) ≤ x.toInt ∧ x.toInt < 2 ^ (w - 1) := by
  have h1 := BitVec.le_toInt x
  have h2 := @BitVec.toInt_lt w x
  have h3 := sdc_two_pow_half hw
  rw [sdc_two_pow_int] at h3
  constructor <;> omega

/-- `-A² ≤ a b ≤ A²` for `|a|, |b| ≤ A`. -/
theorem sdc_mul_range {A a b : Int} (ha1 : -A ≤ a) (ha2 : a ≤ A) (hb1 : -A ≤ b) (hb2 : b ≤ A) :
    -(A * A) ≤ a * b ∧ a * b ≤ A * A := by
  have h1 : 0 ≤ (A - a) * (A - b) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (A + a) * (A + b) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0 ≤ (A - a) * (A + b) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0 ≤ (A + a) * (A - b) := Int.mul_nonneg (by omega) (by omega)
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub] at h1
  rw [Int.add_mul, Int.mul_add, Int.mul_add] at h2
  rw [Int.sub_mul, Int.mul_add, Int.mul_add] at h3
  rw [Int.add_mul, Int.mul_sub, Int.mul_sub] at h4
  have c1 := Int.mul_comm a A
  have c2 := Int.mul_comm b A
  have c3 := Int.mul_comm a b
  constructor <;> omega

theorem sdc_bmod_of_range {w : Nat} (hw : 1 ≤ w) {y : Int} (h1 : -2 ^ (w - 1) ≤ y)
    (h2 : y < 2 ^ (w - 1)) : y.bmod (2 ^ w) = y := by
  have h3 := sdc_two_pow_half hw
  rw [sdc_two_pow_int] at h3
  apply Int.bmod_eq_of_le <;> omega

theorem sdc_toInt_bmod_self {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    x.toInt.bmod (2 ^ w) = x.toInt :=
  sdc_bmod_of_range hw (sdc_toInt_range hw x).1 (sdc_toInt_range hw x).2

/-- The high half of a double-width product (`smulhi`'s `extractLsb'`). -/
theorem sdc_extract_hi_eq {w : Nat} (z : BitVec (w + w)) :
    z.extractLsb' w w = BitVec.ofInt w (z.toInt / 2 ^ w) := by
  apply BitVec.eq_of_toNat_eq
  have hz := z.isLt
  have h2 := sdc_two_pow_int w
  have hpos : (0 : Int) < 2 ^ w := by rw [h2]; exact_mod_cast Nat.two_pow_pos w
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow,
    BitVec.toInt_eq_msb_cond]
  have e : ∀ N : Nat, ((((N : Int) / 2 ^ w) % ((2 ^ w : Nat) : Int)).toNat) = N / 2 ^ w % 2 ^ w := by
    intro N
    rw [h2, ← Int.natCast_ediv, ← Int.natCast_emod, Int.toNat_natCast]
  split
  · have hc : (z.toNat : Int) - ((2 ^ (w + w) : Nat) : Int) =
        (z.toNat : Int) + (-(2 ^ w : Int)) * 2 ^ w := by
      rw [Nat.pow_add, Int.natCast_mul, ← h2, Int.neg_mul]; omega
    rw [hc, Int.add_mul_ediv_right _ _ (by omega)]
    have hd : (z.toNat : Int) / 2 ^ w + -(2 ^ w : Int) =
        (z.toNat : Int) / 2 ^ w + (-1) * ((2 ^ w : Nat) : Int) := by rw [← h2]; omega
    rw [hd, Int.add_mul_emod_self_right, e]
  · exact e _

theorem sdc_smulhi_eq {w : Nat} (hw : 1 ≤ w) (x y : BitVec w) :
    Sem.smulhi x y = BitVec.ofInt w (x.toInt * y.toInt / 2 ^ w) := by
  unfold Sem.smulhi
  rw [sdc_extract_hi_eq, BitVec.toInt_mul, BitVec.toInt_signExtend, BitVec.toInt_signExtend,
    Nat.min_eq_right (Nat.le_add_left w w), sdc_toInt_bmod_self hw, sdc_toInt_bmod_self hw]
  congr 2
  obtain ⟨h1, h2⟩ := sdc_toInt_range hw x
  obtain ⟨h3, h4⟩ := sdc_toInt_range hw y
  obtain ⟨r1, r2⟩ := sdc_mul_range (A := 2 ^ (w - 1)) h1 (by omega) h3 (by omega)
  have hA0 : (0 : Int) < 2 ^ (w - 1) := by rw [sdc_two_pow_int]; exact_mod_cast Nat.two_pow_pos _
  have hf := Int.mul_pos hA0 hA0
  have e : ((2 ^ (w + w) : Nat) : Int) = 4 * (2 ^ (w - 1) * 2 ^ (w - 1)) := by
    rw [← sdc_two_pow_int, ← Int.pow_add, show w + w = 2 + (w - 1 + (w - 1)) by omega, Int.pow_add]
    simp only [Int.reducePow]
  apply Int.bmod_eq_of_le <;> omega

theorem sdc_smulhi_toInt {w : Nat} (hw : 1 ≤ w) (x y : BitVec w) :
    (Sem.smulhi x y).toInt = x.toInt * y.toInt / 2 ^ w := by
  rw [sdc_smulhi_eq hw, BitVec.toInt_ofInt]
  obtain ⟨h1, h2⟩ := sdc_toInt_range hw x
  obtain ⟨h3, h4⟩ := sdc_toInt_range hw y
  obtain ⟨r1, r2⟩ := sdc_mul_range (A := 2 ^ (w - 1)) h1 (by omega) h3 (by omega)
  have hA := sdc_two_pow_half hw
  have hA0 : (0 : Int) < 2 ^ (w - 1) := by rw [sdc_two_pow_int]; exact_mod_cast Nat.two_pow_pos _
  have l1 : -(2 ^ (w - 1)) ≤ x.toInt * y.toInt / 2 ^ w := by
    apply Int.le_ediv_of_mul_le (by omega)
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 2 ^ (w - 1) by omega) (Int.le_of_lt hA0)
    rw [hA]; rw [Int.neg_mul, Int.mul_comm (2 ^ (w - 1)) (2 * 2 ^ (w - 1))]
    rw [Int.mul_assoc]; omega
  have l2 : x.toInt * y.toInt / 2 ^ w < 2 ^ (w - 1) := by
    apply Int.ediv_lt_of_lt_mul (by omega)
    rw [hA, Int.mul_comm (2 ^ (w - 1)) (2 * 2 ^ (w - 1)), Int.mul_assoc]
    have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ 2 ^ (w - 1) by omega) (Int.le_of_lt hA0)
    omega
  exact sdc_bmod_of_range hw l1 l2

/-- The sign correction `q + (q >>> (w - 1))` adds one to a negative `q`. -/
theorem sdc_sign_fix {w : Nat} (hw : 2 ≤ w) (q : BitVec w) :
    (q + q >>> (w - 1)).toInt = q.toInt + if q.toInt < 0 then 1 else 0 := by
  have hq := q.isLt
  have hA := sdc_two_pow_half (w := w) (by omega)
  rw [sdc_two_pow_int, sdc_two_pow_int] at hA
  have hA' : 2 ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast hA
  have hA1 : 2 ≤ 2 ^ (w - 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show 1 ≤ w - 1 by omega); simpa using this
  rw [BitVec.toInt_add, BitVec.toInt_eq_msb_cond q, BitVec.msb_eq_decide]
  have hr : (q >>> (w - 1)).toNat = q.toNat / 2 ^ (w - 1) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hm : 2 ^ (w - 1) ≤ q.toNat
  · have h1 : q.toNat / 2 ^ (w - 1) = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    have hr1 : (q >>> (w - 1)).toInt = 1 := by
      rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, hr, h1]
      simp only [show ¬ 2 ^ (w - 1) ≤ 1 by omega, decide_false]; simp
    rw [hr1]
    simp only [hm, decide_true, ite_true]
    simp only [show (q.toNat : Int) - ((2 ^ w : Nat) : Int) < 0 by omega, ↓reduceIte]
    apply sdc_bmod_of_range (by omega) <;> rw [sdc_two_pow_int] <;> omega
  · have h1 : q.toNat / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by omega)
    have hr1 : (q >>> (w - 1)).toInt = 0 := by
      rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, hr, h1]
      simp only [show ¬ 2 ^ (w - 1) ≤ 0 by omega, decide_false]; simp
    rw [hr1]
    simp only [hm, decide_false]
    simp only [Bool.false_eq_true, ite_false]
    simp only [show ¬ ((q.toNat : Int) < 0) by omega, ↓reduceIte]
    apply sdc_bmod_of_range (by omega) <;> rw [sdc_two_pow_int] <;> omega

/-- The shift and sign correction of the signed sequence compute `x sdiv b` from `q2`. -/
theorem sdc_sdiv_of_q2 {w : Nat} (hw : 2 ≤ w) {x b q2 : BitVec w} {s : Nat}
    (hb : b ≠ -1#w)
    (h : q2.toInt / 2 ^ s + (if q2.toInt / 2 ^ s < 0 then 1 else 0) = x.toInt.tdiv b.toInt) :
    x.sdiv b = q2.sshiftRight s + (q2.sshiftRight s) >>> (w - 1) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr hb), sdc_sign_fix hw, BitVec.toInt_sshiftRight,
    Int.shiftRight_eq_div_pow, ← sdc_two_pow_int, h]

/-- `x srem b = x - (x sdiv b) * b`. -/
theorem sdc_srem_of_sdiv {w : Nat} (hw : 1 ≤ w) (x b : BitVec w) (hb : b ≠ -1#w) :
    x.srem b = x - x.sdiv b * b := by
  apply BitVec.eq_of_toInt_eq
  have e : (x - x.sdiv b * b).toInt = (x.toInt.tmod b.toInt).bmod (2 ^ w) := by
    rw [BitVec.toInt_sub, BitVec.toInt_mul, BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr hb),
      Int.sub_bmod_bmod, Int.tmod_def, Int.mul_comm]
  rw [e, ← BitVec.toInt_srem, sdc_toInt_bmod_self hw]

theorem sdc_asU64_of {y : Int} (h0 : 0 ≤ y) (h1 : y < 2 ^ 64) : Rust.asU64 y = y := by
  simp only [Rust.asU64, BitVec.toNat_ofInt]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  exact Int.emod_eq_of_lt h0 (by simpa using h1)

theorem sdc_asU64_asI64_of {y : Int} (h0 : 0 ≤ y) (h1 : y < 2 ^ 64) :
    Rust.asU64 (Rust.asI64 y) = y := by
  simp only [Rust.asU64, Rust.asI64, BitVec.toNat_ofInt, BitVec.toInt_ofInt, Int.bmod_emod]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  exact Int.emod_eq_of_lt h0 (by simpa using h1)

/-- The magic numbers of a signed divisor `d` (nonzero, `|d|` not a power of two, the facts
`i64_is_any_sign_power_of_two d = false` checks): `DivConst.magicS_spec`. -/
theorem sdc_magicS {w : Nat} (hw : 3 ≤ w) (hw64 : w ≤ 64) {d : Int} (hlo : -2 ^ (w - 1) ≤ d)
    (hhi : d < 2 ^ (w - 1)) (hnz : d ≠ 0) (hc1 : Rust.isPow2 (Rust.asU64 d) = false)
    (hc2 : Rust.isPow2 (Rust.asU64 (Rust.asI64 (-d))) = false) :
    ∃ (m : Int) (s : Nat), Rust.magicS w d = (m, (s : Int)) ∧ -2 ^ (w - 1) ≤ m ∧
      m < 2 ^ (w - 1) ∧ s < w ∧
      ∀ x : Int, -2 ^ (w - 1) ≤ x → x < 2 ^ (w - 1) →
        -2 ^ (w - 1) ≤ (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) ∧
        (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) < 2 ^ (w - 1) ∧
        (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) / 2 ^ s +
          (if (if 0 < d ∧ m < 0 then x * m / 2 ^ w + x
            else if d < 0 ∧ 0 < m then x * m / 2 ^ w - x else x * m / 2 ^ w) / 2 ^ s < 0
            then 1 else 0) = x.tdiv d := by
  have h63 : (2 : Int) ^ (w - 1) ≤ 2 ^ 63 := by
    rw [sdc_two_pow_int, sdc_two_pow_int]
    exact_mod_cast Nat.pow_le_pow_right (by decide) (by omega)
  apply DivConst.magicS_spec hw hnz hlo hhi
  apply DivConst.not_pow_of_isPow2
  rcases Int.lt_or_gt_of_ne hnz with h | h
  · rw [sdc_asU64_asI64_of (by omega) (by omega)] at hc2
    rwa [show (d.natAbs : Int) = -d by omega]
  · rw [sdc_asU64_of (by omega) (by omega)] at hc1
    rwa [show (d.natAbs : Int) = d by omega]

theorem sdc_iconst_s64 (c : Int) (h1 : -2^63 ≤ c) (h2 : c < 2^63) :
    Rust.sext 64 (Rust.asI64 (Rust.band64 (Rust.asU64 c) (2 ^ 64 - 1))) = c := by
  simp only [Rust.sext, Rust.asI64, Rust.band64, Rust.asU64]
  simp
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Int.bmod_def]
  split <;> omega

theorem sdc_iconst_s32 (c : Int) (h1 : -2^31 ≤ c) (h2 : c < 2^31) :
    Rust.sext 32 (Rust.asI64 (Rust.band64 (Rust.asU64 c) (2 ^ 32 - 1))) = c := by
  simp only [Rust.sext, Rust.asI64, Rust.band64, Rust.asU64]
  simp
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Int.bmod_def]
  split <;> split <;> omega

theorem sdc_imm_toInt64 {c y : Int} (h : Rust.sext 64 (Rust.asI64 y) = c) :
    (BitVec.ofInt 64 (Rust.asI64 y)).toInt = c := by
  unfold Rust.sext at h
  simp only [show 64 ≥ 64 by decide, ↓reduceIte] at h
  rw [← h, Rust.asI64, BitVec.ofInt_toInt]

theorem sdc_imm_toInt32 {c y : Int} (h : Rust.sext 32 (Rust.asI64 y) = c) :
    (BitVec.ofInt 32 (Rust.asI64 y)).toInt = c := by
  unfold Rust.sext at h
  simp only [show ¬ (32 ≥ 64) by decide, ↓reduceIte] at h
  exact h

theorem sdc_toNat_of_toInt {w : Nat} {S : BitVec w} {s : Nat} (h : S.toInt = s) : S.toNat = s := by
  have := S.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h
  split at h <;> omega

theorem sdc_shift {w : Nat} {S : BitVec w} {s : Nat} (h : S.toInt = s) (hs : s < w) :
    Sem.shiftAmt w S = s := by
  unfold Sem.shiftAmt; rw [sdc_toNat_of_toInt h, Nat.mod_eq_of_lt hs]

/-- `q3 = q2 >>ₛ s`, `q3 + (q3 >>> (w - 1))` is `a sdiv b` when `q2` is the magic product. -/
theorem sdc_sdiv_seq {w : Nat} (hw : 2 ≤ w) {a b q2 S T : BitVec w} {s : Nat} {Q : Int}
    (hS : S.toInt = s) (hs : s < w) (hT : T.toInt = ((w - 1 : Nat) : Int)) (hb : b ≠ -1#w)
    (hq2 : q2.toInt = Q)
    (h : Q / 2 ^ s + (if Q / 2 ^ s < 0 then 1 else 0) = a.toInt.tdiv b.toInt) :
    a.sdiv b = Sem.binary .iadd (Sem.sshr q2 S) (Sem.ushr (Sem.sshr q2 S) T) := by
  simp only [Sem.binary, Sem.iadd, Sem.sshr, Sem.ushr, sdc_shift hS hs, sdc_shift hT (by omega)]
  exact sdc_sdiv_of_q2 hw hb (by rw [hq2]; exact h)

theorem sdc_q2_none {w : Nat} (hw : 1 ≤ w) {a M : BitVec w} {m : Int} (hM : M.toInt = m) :
    (Sem.binary .smulhi a M).toInt = a.toInt * m / 2 ^ w := by
  simp only [Sem.binary]; rw [sdc_smulhi_toInt hw, hM]

theorem sdc_q2_add {w : Nat} (hw : 1 ≤ w) {a M : BitVec w} {m : Int} (hM : M.toInt = m)
    (r1 : -2 ^ (w - 1) ≤ a.toInt * m / 2 ^ w + a.toInt)
    (r2 : a.toInt * m / 2 ^ w + a.toInt < 2 ^ (w - 1)) :
    (Sem.binary .iadd (Sem.binary .smulhi a M) a).toInt = a.toInt * m / 2 ^ w + a.toInt := by
  simp only [Sem.binary, Sem.iadd]
  rw [BitVec.toInt_add, sdc_smulhi_toInt hw, hM]; exact sdc_bmod_of_range hw r1 r2

theorem sdc_q2_sub {w : Nat} (hw : 1 ≤ w) {a M : BitVec w} {m : Int} (hM : M.toInt = m)
    (r1 : -2 ^ (w - 1) ≤ a.toInt * m / 2 ^ w - a.toInt)
    (r2 : a.toInt * m / 2 ^ w - a.toInt < 2 ^ (w - 1)) :
    (Sem.binary .isub (Sem.binary .smulhi a M) a).toInt = a.toInt * m / 2 ^ w - a.toInt := by
  simp only [Sem.binary, Sem.isub]
  rw [BitVec.toInt_sub, sdc_smulhi_toInt hw, hM]; exact sdc_bmod_of_range hw r1 r2

/-- `a - qf * d` (`apply_div_const_magic_*_finish`, `srem`), after `sdc_srem_of_sdiv`. -/
theorem sdc_srem_seq {w : Nat} {a b qf D : BitVec w} (hD : D.toInt = b.toInt)
    (hq : a.sdiv b = qf) :
    a - a.sdiv b * b = Sem.binary .isub a (Sem.binary .imul qf D) := by
  have : D = b := BitVec.eq_of_toInt_eq hD
  subst this
  simp only [Sem.binary, Sem.isub, Sem.imul]
  rw [hq]

theorem sdc_ne_neg_one_of {d : Int} (hc2 : Rust.isPow2 (Rust.asU64 (Rust.asI64 (-d))) = false) :
    d ≠ -1 := by
  rintro rfl
  rw [sdc_asU64_asI64_of (by decide) (by decide)] at hc2
  exact DivConst.not_pow_of_isPow2 (d := 1) hc2 0 rfl

theorem sdc_ne_allOnes {w : Nat} (hw : 1 ≤ w) {b : BitVec w} (h : b.toInt ≠ -1) :
    b ≠ BitVec.allOnes w := by
  rintro rfl; apply h; rw [BitVec.toInt_allOnes]; simp; omega

theorem sdc_ne_neg_one {w : Nat} (hw : 1 ≤ w) {b : BitVec w} (h : b.toInt ≠ -1) : b ≠ -1#w := by
  rw [BitVec.neg_one_eq_allOnes]; exact sdc_ne_allOnes hw h

theorem sdc_ne_zero {w : Nat} {b : BitVec w} (h : b.toInt ≠ 0) : b ≠ 0#w := by
  rintro rfl; simp at h


/-! ## Rules -/

/-- Phase 3 with extra rewrite facts, then the result destructured (`skel_rhs_dc`). -/
syntax "sdc_rhs" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| sdc_rhs [$ts,*]) => `(tactic| (
      try opt_eval hev [$ts,*]
      repeat' (first
        | (rw [Isle.Interp.matchAll.eq_2] at hev; opt_eval hev [$ts,*])
        | (rw [Isle.Interp.matchAll.eq_1] at hev; opt_eval hev [$ts,*])
        | (split at hev <;> try opt_norm hev [$ts,*]))
      all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
      opt_destruct
      all_goals subst_vars
      all_goals (
        simp only [Except.ok.injEq, Prod.mk.injEq] at hev
        obtain ⟨rfl, rfl, rfl⟩ := hev
        simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
        subst hw)
      all_goals opt_types))

/-- Phase 3 without case splits: evaluate as far as the given facts decide (the shared prefix of
the sign cases). -/
syntax "sdc_eval" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
  Lean.Parser.Tactic.simpLemma),* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| sdc_eval [$ts,*]) => `(tactic| (
      try opt_eval hev [$ts,*]
      repeat' (first
        | (rw [Isle.Interp.matchAll.eq_2] at hev; opt_eval hev [$ts,*])
        | (rw [Isle.Interp.matchAll.eq_1] at hev; opt_eval hev [$ts,*]))))

set_option hygiene false in
/-- Phase 4 for a signed `div` replaced by the magic sequence: no trap (the divisor is neither `0`
nor `-1`), then the value goal, left to the caller. -/
macro "sdc_div" : tactic => `(tactic| (
  skel_good
  apply skel_div_rwv (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den))
  intro a b ha hb
  opt_destruct
  all_goals subst_vars
  skel_imm
  refine ⟨?_, ?_⟩
  · simp only [divOk]
    simp [sdc_ne_zero hdz, sdc_ne_allOnes (by decide) hn1]
  simp only [divVal]
  apply hle4
  try dsimp only
  apply GraphOk.make_val hG (by opt_P)
  divc_node))

set_option hygiene false in
/-- The value goal: `sdc_sdiv_seq` with the `q2` of the case (`sdc_q2_add`/`sub`/`none`), under
`sdc_srem_seq` for `srem`. `it` is the immediate lemma of the width. -/
macro "sdc_fin " w:num it:ident : tactic => `(tactic| (
  apply val_congr
  obtain ⟨r1, r2, hc⟩ := hcorr (BitVec.toInt (n := $w) a)
    (sdc_toInt_range (w := $w) (by decide) a).1 (sdc_toInt_range (w := $w) (by decide) a).2
  simp only [hd0, hd1, hm, true_and, and_true, false_and, and_false, ↓reduceIte] at r1 r2 hc
  have hq := fun (q2 : BitVec _) (hq2 : q2.toInt = _) =>
    sdc_sdiv_seq (a := a) (b := dv) (by decide) ($it hsc) hs (by exact $it hC)
      (sdc_ne_neg_one (by decide) hn1) hq2 hc
  first
    | (rw [sdc_srem_of_sdiv (by decide) _ _ (sdc_ne_neg_one (by decide) hn1)]
       refine sdc_srem_seq (by exact $it hdc) (hq _ ?_)
       first
         | exact sdc_q2_add (by decide) ($it hmc) r1 r2
         | exact sdc_q2_sub (by decide) ($it hmc) r1 r2
         | exact sdc_q2_none (by decide) ($it hmc))
    | (refine hq _ ?_
       first
         | exact sdc_q2_add (by decide) ($it hmc) r1 r2
         | exact sdc_q2_sub (by decide) ($it hmc) r1 r2
         | exact sdc_q2_none (by decide) ($it hmc))))

set_option hygiene false in
/-- Phases 3-4 of the signed rules at width `w` (`ic` the `iconst_s` range lemma, `it` the
immediate lemma, `c` the sign-bit shift `w - 1`), after the left-hand side: the divisor `dv` with
the facts `hnz`, `hc1`, `hc2` of `i64_extract_non_zero` and `i64_is_any_sign_power_of_two`. The
magic numbers come from `sdc_magicS`; per sign of `dv` and of the multiplier (the fix-up rule of
`apply_div_const_magic_*_add_sub` that fires) the right-hand side is evaluated and closed by
`sdc_fin`. -/
macro "sdc_rest " w:num ic:ident it:ident c:num : tactic => `(tactic| (
  obtain ⟨hb1, hb2⟩ := sdc_toInt_range (w := $w) (by decide) dv
  have hdz : dv.toInt ≠ 0 := by simp at hnz; exact hnz
  have hn1 : dv.toInt ≠ -1 := sdc_ne_neg_one_of (by simp at hc2; exact hc2)
  obtain ⟨m, s, hmag, hm1, hm2, hs, hcorr⟩ := sdc_magicS (w := $w) (d := BitVec.toInt (n := $w) dv)
    (by decide) (by decide) hb1 hb2 hdz (by simp at hc1; exact hc1) (by simp at hc2; exact hc2)
  have hmc := $ic m (by simpa using hm1) (by simpa using hm2)
  have hsc := $ic (s : Int) (by omega) (by omega)
  have hC := $ic $c (by omega) (by omega)
  have hdc := $ic dv.toInt (by have h := hb1; simp at h ⊢; exact h)
    (by have h := hb2; simp at h ⊢; exact h)
  have hdc' := $ic (BitVec.toInt (n := $w) dv) (by simpa using hb1) (by simpa using hb2)
  have hsu : Rust.asU32 (s : Int) = (s : Int) := by
    simp only [Rust.asU32, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  sdc_eval [hmag, hmc, hsc, hC, hdc, hdc', hsu, beq_self_eq_true, Ty.width, gt_iff_lt,
    Nat.reduceBEq, divc_true_beq_true, divc_false_beq_true]
  -- Derive the sign cases from the nonzero fact directly. Transport to the
  -- literal-width presentation by definitional equality, not omega atom matching.
  rcases (show (0 < BitVec.toInt (n := $w) dv ∧ ¬ BitVec.toInt (n := $w) dv < 0 ∧
      0 < dv.toInt ∧ ¬ dv.toInt < 0) ∨ (BitVec.toInt (n := $w) dv < 0 ∧
      ¬ 0 < BitVec.toInt (n := $w) dv ∧ dv.toInt < 0 ∧ ¬ 0 < dv.toInt) from
        (Int.lt_or_gt_of_ne hdz).elim
          (fun hneg => Or.inr ⟨hneg, Int.lt_asymm hneg, hneg, Int.lt_asymm hneg⟩)
          (fun hpos => Or.inl ⟨hpos, Int.lt_asymm hpos, hpos, Int.lt_asymm hpos⟩)) with
    ⟨hd0, hd1, hd0w, hd1w⟩ | ⟨hd0, hd1, hd0w, hd1w⟩
  · sdc_eval [hmag, hd0, hd1, hd0w, hd1w, hmc, hsc, hC, hdc, hdc', hsu, beq_self_eq_true,
      Ty.width, gt_iff_lt, Nat.reduceBEq, divc_true_beq_true, divc_false_beq_true]
    rcases (show m < 0 ∨ ¬ m < 0 by omega) with hm | hm
    all_goals (
      sdc_rhs [hmag, hd0, hd1, hd0w, hd1w, hm, hmc, hsc, hC, hdc, hdc', hsu, beq_self_eq_true,
        Ty.width, gt_iff_lt, Nat.reduceBEq, divc_true_beq_true, divc_false_beq_true]
      all_goals sdc_div
      all_goals sdc_fin $w $it)
  · sdc_eval [hmag, hd0, hd1, hd0w, hd1w, hmc, hsc, hC, hdc, hdc', hsu, beq_self_eq_true,
      Ty.width, gt_iff_lt, Nat.reduceBEq, divc_true_beq_true, divc_false_beq_true]
    rcases (show 0 < m ∨ ¬ 0 < m by omega) with hm | hm
    all_goals (
      sdc_rhs [hmag, hd0, hd1, hd0w, hd1w, hm, hmc, hsc, hC, hdc, hdc', hsu, beq_self_eq_true,
        Ty.width, gt_iff_lt, Nat.reduceBEq, divc_true_beq_true, divc_false_beq_true]
      all_goals sdc_div
      all_goals sdc_fin $w $it)))

open Lean Elab Tactic in
/-- Run a tactic without recording info trees. Lean keeps every command's info tree (each
intermediate goal of every tactic step) until the module is done; for these long evaluations
that is several GB per theorem. -/
elab "sdc_noinfo " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

set_option hygiene false in
/-- The signed template at width 64. -/
macro "skel_auto_dcs64 " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals (skel_rule_iflets; skel_iflets)
  all_goals skel_imm
  all_goals (try (simp at *; done))
  rename_i dv _ _ _ _ hnz hc1 hc2
  sdc_rest 64 sdc_iconst_s64 sdc_imm_toInt64 63))

set_option hygiene false in
/-- The signed template at width 32 (the extra `inI32` fact of `i32_from_i64` is dropped). -/
macro "skel_auto_dcs32 " r:ident : tactic => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals (skel_rule_iflets; skel_iflets)
  all_goals skel_imm
  all_goals (try (simp at *; done))
  rename_i dv _ _ _ _ hnz _ hc1 hc2
  sdc_rest 32 sdc_iconst_s32 sdc_imm_toInt32 31))

set_option maxHeartbeats 64000000 in
theorem ok_rule_arithmetic_122 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_122 := by
  sdc_noinfo skel_auto_dcs32 rule_arithmetic_122

set_option maxHeartbeats 64000000 in
theorem ok_rule_arithmetic_125 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_125 := by
  sdc_noinfo skel_auto_dcs64 rule_arithmetic_125

set_option maxHeartbeats 64000000 in
theorem ok_rule_arithmetic_165 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_165 := by
  sdc_noinfo skel_auto_dcs32 rule_arithmetic_165

set_option maxHeartbeats 64000000 in
theorem ok_rule_arithmetic_168 {p : Isle.Program} (hd : Data p) :
    SkelRuleOk p rule_arithmetic_168 := by
  sdc_noinfo skel_auto_dcs64 rule_arithmetic_168

/-! ## Non-vacuity

The small-width examples inhabit the arithmetic helpers' premises, including signed minima
and both correction directions. The final examples inhabit the actual signed-rule guards
at both production widths and distinguish all four divisor/multiplier sign branches.
End-to-end rule firing is exercised by the optimizer smoke, rather than evaluating the
generated interpreter inside a proof.
-/

example : (2 : Int) ^ 4 = ((2 ^ 4 : Nat) : Int) := sdc_two_pow_int 4

example : (2 : Int) ^ 4 = 2 * 2 ^ (4 - 1) := sdc_two_pow_half (by decide)

example : -2 ^ (4 - 1) ≤ (8#4).toInt ∧ (8#4).toInt < 2 ^ (4 - 1) :=
  sdc_toInt_range (by decide) _

example : -(8 * 8 : Int) ≤ (-8) * 7 ∧ (-8 : Int) * 7 ≤ 8 * 8 :=
  sdc_mul_range (by decide) (by decide) (by decide) (by decide)

example : (-8 : Int).bmod (2 ^ 4) = -8 :=
  sdc_bmod_of_range (w := 4) (by decide) (by decide) (by decide)

example : (8#4).toInt.bmod (2 ^ 4) = (8#4).toInt :=
  sdc_toInt_bmod_self (by decide) _

example : (192#8).extractLsb' 4 4 = BitVec.ofInt 4 ((192#8).toInt / 2 ^ 4) :=
  sdc_extract_hi_eq _

example : Sem.smulhi (8#4) (7#4) = BitVec.ofInt 4 ((8#4).toInt * (7#4).toInt / 2 ^ 4) :=
  sdc_smulhi_eq (by decide) _ _

example : (Sem.smulhi (8#4) (7#4)).toInt = (8#4).toInt * (7#4).toInt / 2 ^ 4 :=
  sdc_smulhi_toInt (by decide) _ _

example : ((8#4) + (8#4) >>> 3).toInt =
    (8#4).toInt + if (8#4).toInt < 0 then 1 else 0 :=
  sdc_sign_fix (by decide) _

example : (8#4).sdiv (3#4) = (10#4).sshiftRight 1 + ((10#4).sshiftRight 1) >>> 3 :=
  sdc_sdiv_of_q2 (by decide) (by decide) (by decide)

example : (8#4).srem (3#4) = (8#4) - (8#4).sdiv (3#4) * (3#4) :=
  sdc_srem_of_sdiv (by decide) _ _ (by decide)

example : Rust.asU64 7 = 7 := sdc_asU64_of (by decide) (by decide)

example : Rust.asU64 (Rust.asI64 (2 ^ 64 - 1)) = 2 ^ 64 - 1 :=
  sdc_asU64_asI64_of (by decide) (by decide)

example : Rust.sext 64 (Rust.asI64 (Rust.band64 (Rust.asU64 (-7)) (2 ^ 64 - 1))) = -7 :=
  sdc_iconst_s64 _ (by decide) (by decide)

example : Rust.sext 32 (Rust.asI64 (Rust.band64 (Rust.asU64 (-7)) (2 ^ 32 - 1))) = -7 :=
  sdc_iconst_s32 _ (by decide) (by decide)

example : (BitVec.ofInt 64 (Rust.asI64 (-7))).toInt = -7 :=
  sdc_imm_toInt64 (by decide)

example : (BitVec.ofInt 32 (Rust.asI64 (-7))).toInt = -7 :=
  sdc_imm_toInt32 (by decide)

example : (3#4).toNat = 3 := sdc_toNat_of_toInt (by decide)

example : Sem.shiftAmt 4 (3#4) = 3 := sdc_shift (by decide) (by decide)

example : (8#4).sdiv (3#4) =
    Sem.binary .iadd (Sem.sshr (10#4) (1#4)) (Sem.ushr (Sem.sshr (10#4) (1#4)) (3#4)) :=
  sdc_sdiv_seq (s := 1) (Q := -6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

example : (Sem.binary .smulhi (8#4) (7#4)).toInt = (8#4).toInt * 7 / 2 ^ 4 :=
  sdc_q2_none (by decide) (by decide)

example : (Sem.binary .iadd (Sem.binary .smulhi (8#4) (9#4)) (8#4)).toInt =
    (8#4).toInt * (-7) / 2 ^ 4 + (8#4).toInt :=
  sdc_q2_add (by decide) (by decide) (by decide) (by decide)

example : (Sem.binary .isub (Sem.binary .smulhi (8#4) (7#4)) (8#4)).toInt =
    (8#4).toInt * 7 / 2 ^ 4 - (8#4).toInt :=
  sdc_q2_sub (by decide) (by decide) (by decide) (by decide)

example : (8#4) - (8#4).sdiv (3#4) * (3#4) =
    Sem.binary .isub (8#4) (Sem.binary .imul (14#4) (3#4)) :=
  sdc_srem_seq (by decide) (by decide)

example : (-7 : Int) ≠ -1 := sdc_ne_neg_one_of (by decide)

example : (9#4) ≠ BitVec.allOnes 4 := sdc_ne_allOnes (by decide) (by decide)

example : (9#4) ≠ -1#4 := sdc_ne_neg_one (by decide) (by decide)

example : (9#4) ≠ 0#4 := sdc_ne_zero (by decide)

/-- The nonzero, representability and two non-power-of-two guards are simultaneously
satisfiable for each production width and each sign/correction fixture. -/
example : ∀ w ∈ [32, 64], ∀ d ∈ ([3, 7, 15, -3, -5, -7, -15] : List Int),
    3 ≤ w ∧ w ≤ 64 ∧ -2 ^ (w - 1) ≤ d ∧ d < 2 ^ (w - 1) ∧ d ≠ 0 ∧
    Rust.isPow2 (Rust.asU64 d) = false ∧
    Rust.isPow2 (Rust.asU64 (Rust.asI64 (-d))) = false := by native_decide

/-- `sdc_magicS` applies to real positive and negative divisors, not only hypothetical
magic constants. Its correction equation holds for every dividend in the signed range. -/
example : ∃ (m : Int) (s : Nat), Rust.magicS 32 7 = (m, (s : Int)) ∧ s < 32 := by
  obtain ⟨m, s, hm, _, _, hs, _⟩ :=
    sdc_magicS (w := 32) (d := 7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact ⟨m, s, hm, hs⟩

example : ∃ (m : Int) (s : Nat), Rust.magicS 64 (-7) = (m, (s : Int)) ∧ s < 64 := by
  obtain ⟨m, s, hm, _, _, hs, _⟩ :=
    sdc_magicS (w := 64) (d := -7) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact ⟨m, s, hm, hs⟩

/-- Positive divisor: the multiplier can require adding the dividend or no correction. -/
example : (Rust.magicS 32 7).1 < 0 ∧ 0 < (Rust.magicS 32 3).1 ∧
    (Rust.magicS 64 15).1 < 0 ∧ 0 < (Rust.magicS 64 3).1 := by native_decide

/-- Negative divisor: the multiplier can require subtracting the dividend or no correction. -/
example : 0 < (Rust.magicS 32 (-3)).1 ∧ (Rust.magicS 32 (-5)).1 < 0 ∧
    0 < (Rust.magicS 64 (-3)).1 ∧ (Rust.magicS 64 (-5)).1 < 0 := by native_decide

end Opt.Proof

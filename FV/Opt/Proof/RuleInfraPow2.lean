import FV.Opt.Proof.RuleSkelEmbed

/-!
# Helper specifications: powers of two (`imm64_power_of_two`, `u64_ilog2`, `*_trailing_zeros`)

Power-of-two immediates in the normal form of `FV/Opt/Proof/RuleImm.lean`: a matched immediate
`imm64OfBits b` that a rule recognises as a power of two becomes `b = BitVec.twoPow w k` with
`k < w` (`pow2_lhs`), and the helpers the right-hand sides call on it evaluate to `k`.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

/-! ## `u64::is_power_of_two`, `ilog2`, `trailing_zeros` on `2 ^ k` -/

theorem pow2_isPow2_natCast (n : Nat) : Rust.isPow2 (n : Int) = true ↔ ∃ k, n = 2 ^ k := by
  unfold Rust.isPow2
  simp only [Int.toNat_natCast, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨_, h⟩; exact ⟨_, h⟩
  · rintro ⟨k, rfl⟩
    refine ⟨?_, by rw [Nat.log2_two_pow]⟩
    have := Nat.two_pow_pos k
    omega

/-- `u64_is_power_of_two` of the bits of an immediate. -/
theorem pow2_isPow2_toNat_iff {w : Nat} (b : BitVec w) :
    Rust.isPow2 (b.toNat : Int) = true ↔ ∃ k, k < w ∧ b = BitVec.twoPow w k := by
  rw [pow2_isPow2_natCast]
  constructor
  · rintro ⟨k, hk⟩
    have hlt : k < w := by
      have := b.isLt; rw [hk] at this; exact (Nat.pow_lt_pow_iff_right (by decide)).1 this
    exact ⟨k, hlt, BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_twoPow_of_lt hlt, hk])⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, BitVec.toNat_twoPow_of_lt hk⟩

theorem pow2_ctz64 {k : Nat} (hk : k < 64) : Rust.ctz64 ((2 ^ k : Nat) : Int) = k := by
  unfold Rust.ctz64 Rust.asU64
  have h1 : ((BitVec.ofInt 64 ((2 ^ k : Nat) : Int)).toNat : Int).toNat = 2 ^ k := by
    rw [BitVec.ofInt_natCast, Int.toNat_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  simp only [h1]
  have h0 : (2 ^ k == 0) = false := by simp
  rw [h0]
  simp only [Bool.false_eq_true, ite_false]
  rw [ctz64_go k (2 ^ k) 0 64 (fun i hi => Nat.testBit_two_pow_of_ne (by omega))
    Nat.testBit_two_pow_self hk]
  omega

theorem pow2_u64Ilog2 (k : Nat) : Rust.u64Ilog2 ((2 ^ k : Nat) : Int) = .ok (k : Int) := by
  unfold Rust.u64Ilog2
  have := Nat.two_pow_pos k
  split
  · rw [Int.toNat_natCast, Nat.log2_two_pow]; rfl
  · omega

theorem pow2_width_le_64 {t : Ty} (ht : t ≠ .i128) : t.width ≤ 64 := by
  cases t <;> simp_all [Ty.width]

/-- `u64_is_power_of_two` of the bits of an immediate at a non-`i128` type (with the bound
`k < 64` the helper lemmas discharge). -/
theorem pow2_isPow2_toNat_ty {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.isPow2 (b.toNat : Int) = true ↔
      ∃ k, k < t.width ∧ k < 64 ∧ b = BitVec.twoPow t.width k := by
  rw [pow2_isPow2_toNat_iff]
  have := pow2_width_le_64 ht
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by omega, rfl⟩
  · rintro ⟨k, hk, -, rfl⟩; exact ⟨k, hk, rfl⟩

theorem pow2_natCast_gt_one (k : Nat) : (((2 ^ k : Nat) : Int) > 1) ↔ 0 < k := by
  have e : (((2 ^ k : Nat) : Int) > 1) ↔ 1 < 2 ^ k := by omega
  rw [e]
  constructor
  · intro h; rcases Nat.eq_zero_or_pos k with rfl | h'
    · simp at h
    · exact h'
  · intro h; exact Nat.one_lt_two_pow (by omega)

/-! ## Helper arithmetic on small non-negative values (side conditions by `omega`) -/

theorem pow2_checkedSubU_ok {fn : String} {a b : Int} (h : b ≤ a) :
    Rust.checkedSubU fn a b = .ok (a - b) := by
  simp [Rust.checkedSubU, h]

theorem pow2_asU64_of_lt {a : Int} (h0 : 0 ≤ a) (h : a < 2 ^ 64) : Rust.asU64 a = a := by
  unfold Rust.asU64
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt h0 (by simpa using h)]

theorem pow2_asI64_of_lt {a : Int} (h0 : 0 ≤ a) (h : a < 2 ^ 63) : Rust.asI64 a = a := by
  simp only [Rust.asI64, BitVec.toInt_ofInt]
  simp only [Nat.reducePow, Int.reducePow] at h ⊢
  rw [Int.bmod_eq_emod_of_lt] <;> rw [Int.emod_eq_of_lt] <;> omega

theorem pow2_decide_le_true {a b : Int} (h : a ≤ b) : decide (a ≤ b) = true := decide_eq_true h

theorem pow2_band64_mask {a : Int} {w : Nat} (h0 : 0 ≤ a) (h : a < 2 ^ w) (hw : w ≤ 64) :
    Rust.band64 a (2 ^ w - 1) = a := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  have hp : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl
  have hw' : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have h1 := Nat.two_pow_pos w
  have hn : n < 2 ^ w := by omega
  have hm : (2 : Int) ^ w - 1 = ((2 ^ w - 1 : Nat) : Int) := by omega
  rw [Rust.band64, hm, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_and,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hn]

theorem pow2_sext_of_lt {a : Int} {w : Nat} (h0 : 0 ≤ a) (h : a < 2 ^ (w - 1)) (hw : 0 < w) :
    Rust.sext w a = a := by
  unfold Rust.sext
  split
  · rfl
  · rw [BitVec.toInt_ofInt]
    have e : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hp : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
    apply Int.bmod_eq_of_le_mul_two <;> push_cast [e] <;> omega

/-! ## Division by `± 2 ^ k` as shifts and masks -/

theorem pow2_msb_twoPow {w k : Nat} (hk : k + 1 < w) : (BitVec.twoPow w k).msb = false := by
  rw [BitVec.msb_twoPow]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem pow2_msb_neg_twoPow {w k : Nat} (hk : k < w) : (-(BitVec.twoPow w k)).msb = true := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt hk]
  have h1 : 2 ^ k ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h3 := Nat.two_pow_pos k
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [decide_eq_true_eq]
  omega

theorem pow2_sdiv_twoPow {w k : Nat} (hk : k + 1 < w) (x : BitVec w) :
    x.sdiv (BitVec.twoPow w k) = bif x.msb then -((-x) >>> k) else x >>> k := by
  rw [BitVec.sdiv_eq, pow2_msb_twoPow hk]
  cases x.msb <;> simp only [BitVec.udiv_eq, BitVec.udiv_twoPow_eq_of_lt (show k < w by omega),
    Bool.cond_true, Bool.cond_false]

theorem pow2_sdiv_neg_twoPow {w k : Nat} (hk : k < w) (x : BitVec w) :
    x.sdiv (-(BitVec.twoPow w k)) = bif x.msb then (-x) >>> k else -(x >>> k) := by
  rw [BitVec.sdiv_eq, pow2_msb_neg_twoPow hk, BitVec.neg_neg]
  cases x.msb <;> simp only [BitVec.udiv_eq, BitVec.udiv_twoPow_eq_of_lt hk, Bool.cond_true, Bool.cond_false]

theorem pow2_umod_twoPow {w k : Nat} (hk : k < w) (x : BitVec w) :
    x % BitVec.twoPow w k = x &&& (BitVec.twoPow w k - 1#w) := by
  apply BitVec.eq_of_toNat_eq
  have h2 := Nat.two_pow_pos k
  have h3 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h1 : 1#w ≤ BitVec.twoPow w k := by
    rw [BitVec.le_def, BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]
    omega
  rw [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_sub_of_le h1, BitVec.toNat_twoPow_of_lt hk,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3, Nat.and_two_pow_sub_one_eq_mod]

theorem pow2_srem_twoPow {w k : Nat} (hk : k + 1 < w) (x : BitVec w) :
    x.srem (BitVec.twoPow w k) =
      bif x.msb then -((-x) &&& (BitVec.twoPow w k - 1#w)) else x &&& (BitVec.twoPow w k - 1#w) := by
  rw [BitVec.srem_eq, pow2_msb_twoPow hk]
  cases x.msb <;> simp only [pow2_umod_twoPow (show k < w by omega), Bool.cond_true, Bool.cond_false]

theorem pow2_srem_neg_twoPow {w k : Nat} (hk : k < w) (x : BitVec w) :
    x.srem (-(BitVec.twoPow w k)) =
      bif x.msb then -((-x) &&& (BitVec.twoPow w k - 1#w)) else x &&& (BitVec.twoPow w k - 1#w) := by
  rw [BitVec.srem_eq, pow2_msb_neg_twoPow hk, BitVec.neg_neg]
  cases x.msb <;> simp only [pow2_umod_twoPow hk, Bool.cond_true, Bool.cond_false]

/-! ## Sign-extended immediates (`iconst_s`) that are `± 2 ^ k` -/

theorem pow2_asU64_cases {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 64) :
    Rust.asU64 x = if 0 ≤ x then x else x + 2 ^ 64 := by
  unfold Rust.asU64
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  simp only [Nat.reducePow, Int.reducePow] at *
  split <;> omega

theorem pow2_isPow2_asU64 {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63) :
    Rust.isPow2 (Rust.asU64 x) = true ↔
      (∃ j, j ≤ 63 ∧ x = ((2 ^ j : Nat) : Int)) ∨ x = -2 ^ 63 := by
  rw [pow2_asU64_cases h1 (by omega)]
  split
  · rename_i hx
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
    rw [pow2_isPow2_natCast]
    constructor
    · rintro ⟨j, rfl⟩
      refine .inl ⟨j, ?_, rfl⟩
      have : 2 ^ j ≤ 2 ^ 63 := by
        generalize 2 ^ j = m at h2 ⊢; simp only [Int.reducePow] at h2; omega
      exact (Nat.pow_le_pow_iff_right (by decide)).1 this
    · rintro (⟨j, -, h⟩ | h)
      · exact ⟨j, by exact_mod_cast h⟩
      · omega
  · rename_i hx
    have hn : 0 ≤ x + 2 ^ 64 := by omega
    obtain ⟨n, hn'⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hn', pow2_isPow2_natCast]
    constructor
    · rintro ⟨j, rfl⟩
      right
      have hlo : 2 ^ 63 ≤ 2 ^ j ∧ 2 ^ j < 2 ^ 64 := by
        generalize 2 ^ j = m at hn' ⊢; simp only [Int.reducePow, Nat.reducePow] at *; omega
      have h3 := (Nat.pow_le_pow_iff_right (by decide)).1 hlo.1
      have h4 := (Nat.pow_lt_pow_iff_right (by decide)).1 hlo.2
      obtain rfl : j = 63 := by omega
      simp only [Nat.reducePow, Int.reducePow] at hn' ⊢; omega
    · rintro (⟨j, -, h⟩ | h)
      · have : (0 : Int) ≤ ((2 ^ j : Nat) : Int) := Int.natCast_nonneg _
        omega
      · exact ⟨63, by simp only [Nat.reducePow, Int.reducePow] at hn' h ⊢; omega⟩

theorem pow2_two_pow_eq {w : Nat} (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

theorem pow2_toInt_twoPow {w j : Nat} (hj : j < w) :
    (BitVec.twoPow w j).toInt =
      if j + 1 < w then ((2 ^ j : Nat) : Int) else -((2 ^ j : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_twoPow_of_lt hj]
  have e := pow2_two_pow_eq (show 0 < w by omega)
  by_cases h : j + 1 < w
  · have : 2 ^ j < 2 ^ (w - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  · obtain rfl : j = w - 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    rw [e]; generalize 2 ^ (w - 1) = m; push_cast; omega

theorem pow2_toInt_neg_twoPow {w j : Nat} (hj : j < w) :
    (-(BitVec.twoPow w j)).toInt = -((2 ^ j : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt hj]
  have e := pow2_two_pow_eq (show 0 < w by omega)
  have h1 : 2 ^ j ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 := Nat.two_pow_pos j
  rw [e]
  generalize 2 ^ (w - 1) = m at h1 ⊢
  generalize 2 ^ j = n at h1 h3 ⊢
  rw [Nat.mod_eq_of_lt (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    Int.ofNat_sub (by omega)]
  push_cast
  omega

theorem pow2_asU64_asI64 (y : Int) : Rust.asU64 (Rust.asI64 y) = Rust.asU64 y := by
  simp only [Rust.asU64, Rust.asI64, BitVec.ofInt_toInt]

theorem pow2_int_two_pow (n : Nat) : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by
  rw [Int.natCast_pow]; rfl

/-- The `toInt` range of a bit vector of width `0 < w ≤ 64`, against `2 ^ 63`. -/
theorem pow2_toInt_range {w : Nat} (hw : 0 < w) (hw' : w ≤ 64) (b : BitVec w) :
    -((2 ^ (w - 1) : Nat) : Int) ≤ b.toInt ∧ b.toInt < ((2 ^ (w - 1) : Nat) : Int) ∧
      2 ^ (w - 1) ≤ 2 ^ 63 := by
  have h1 := BitVec.le_toInt b
  have h2 := BitVec.toInt_lt (x := b)
  rw [pow2_int_two_pow] at h1 h2
  exact ⟨h1, h2, Nat.pow_le_pow_right (by decide) (by omega)⟩

theorem pow2_isPow2_pos_iff {w : Nat} (hw : 0 < w) (hw' : w ≤ 64) (b : BitVec w) :
    Rust.isPow2 (Rust.asU64 b.toInt) = true ↔
      ∃ k, k < w ∧ k < 64 ∧ b = BitVec.twoPow w k ∧ (k + 1 < w ∨ w = 64) := by
  obtain ⟨h1, h2, h3⟩ := pow2_toInt_range hw hw' b
  rw [pow2_isPow2_asU64 (by rw [pow2_int_two_pow]; omega) (by rw [pow2_int_two_pow]; omega)]
  constructor
  · rintro (⟨j, hj, hb⟩ | hb)
    · have hjw : j + 1 < w := by
        have : 2 ^ j < 2 ^ (w - 1) := by rw [hb] at h2; exact_mod_cast h2
        have := (Nat.pow_lt_pow_iff_right (by decide)).1 this
        omega
      refine ⟨j, by omega, by omega, ?_, .inl hjw⟩
      rw [← BitVec.toInt_inj, pow2_toInt_twoPow (by omega), ite_eq_left_of_eq_true _ _ (eq_true hjw), hb]
    · have hw64 : w = 64 := by
        rw [hb, pow2_int_two_pow] at h1
        have : 2 ^ 63 ≤ 2 ^ (w - 1) := by omega
        have := (Nat.pow_le_pow_iff_right (by decide)).1 this
        omega
      subst hw64
      refine ⟨63, by omega, by omega, ?_, .inr rfl⟩
      rw [← BitVec.toInt_inj, pow2_toInt_twoPow (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hb,
        pow2_int_two_pow]
  · rintro ⟨k, hk, hk64, rfl, hk'⟩
    rw [pow2_toInt_twoPow hk]
    by_cases h : k + 1 < w
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]; exact .inl ⟨k, by omega, rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      obtain rfl : w = 64 := by omega
      obtain rfl : k = 63 := by omega
      right; rw [pow2_int_two_pow]

theorem pow2_isPow2_neg_iff {w : Nat} (hw : 0 < w) (hw' : w ≤ 64) (b : BitVec w) :
    Rust.isPow2 (Rust.asU64 (Rust.asI64 (-b.toInt))) = true ↔
      ∃ k, k < w ∧ k < 64 ∧ b = -BitVec.twoPow w k := by
  obtain ⟨h1, h2, h3⟩ := pow2_toInt_range hw hw' b
  rw [pow2_asU64_asI64, pow2_isPow2_asU64 (by rw [pow2_int_two_pow]; omega)
    (by rw [pow2_int_two_pow]; omega)]
  constructor
  · rintro (⟨j, hj, hb⟩ | hb)
    · have hjw : j < w := by
        have : 2 ^ j ≤ 2 ^ (w - 1) := by
          have : ((2 ^ j : Nat) : Int) ≤ ((2 ^ (w - 1) : Nat) : Int) := by omega
          exact_mod_cast this
        have := (Nat.pow_le_pow_iff_right (by decide)).1 this
        omega
      refine ⟨j, hjw, by omega, ?_⟩
      rw [← BitVec.toInt_inj, pow2_toInt_neg_twoPow hjw]
      omega
    · rw [pow2_int_two_pow] at hb
      omega
  · rintro ⟨k, hk, hk64, rfl⟩
    rw [pow2_toInt_neg_twoPow hk]
    exact .inl ⟨k, by omega, by omega⟩


theorem pow2_neg_twoPow_last {w : Nat} (hw : 0 < w) :
    -(BitVec.twoPow w (w - 1)) = BitVec.twoPow w (w - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h := Nat.two_pow_pos (w - 1)
  rw [BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt (by omega), pow2_two_pow_eq hw]
  generalize 2 ^ (w - 1) = m at h ⊢
  rw [show 2 * m - m = m by omega, Nat.mod_eq_of_lt (by omega)]

theorem pow2_width_pos {t : Ty} (ht : t ≠ .i128) : 0 < t.width := by
  cases t <;> simp_all [Ty.width]

/-- `u64_is_power_of_two (i64_cast_unsigned d)` of a sign-extended immediate `d` (the first rule
of `i64_is_any_sign_power_of_two`): a power of two below the sign bit, or `i64::MIN`. -/
theorem pow2_isPow2_pos_ty {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.isPow2 (Rust.asU64 b.toInt) = true ↔
      (∃ k, k < t.width ∧ k < 64 ∧ k + 1 < t.width ∧ b = BitVec.twoPow t.width k) ∨
        (t.width = 64 ∧ b = -BitVec.twoPow t.width 63) := by
  have hw := pow2_width_le_64 ht
  have hw0 := pow2_width_pos ht
  have hl := pow2_neg_twoPow_last hw0
  rw [pow2_isPow2_pos_iff hw0 hw]
  constructor
  · rintro ⟨k, hk, hk64, rfl, hk' | hk'⟩
    · exact .inl ⟨k, hk, hk64, hk', rfl⟩
    · by_cases h : k + 1 < t.width
      · exact .inl ⟨k, hk, hk64, h, rfl⟩
      · right
        refine ⟨hk', ?_⟩
        obtain rfl : k = 63 := by omega
        rw [show t.width - 1 = 63 by omega] at hl
        exact hl.symm
  · rintro (⟨k, hk, hk64, hk', rfl⟩ | ⟨hk', rfl⟩)
    · exact ⟨k, hk, hk64, rfl, .inl hk'⟩
    · refine ⟨63, by omega, by omega, ?_, .inr hk'⟩
      rw [show t.width - 1 = 63 by omega] at hl
      exact hl

/-- `i64_is_negative_power_of_two` of a sign-extended immediate. -/
theorem pow2_isPow2_neg_ty {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) :
    Rust.isPow2 (Rust.asU64 (Rust.asI64 (-b.toInt))) = true ↔
      ∃ k, k < t.width ∧ k < 64 ∧ b = -BitVec.twoPow t.width k :=
  pow2_isPow2_neg_iff (pow2_width_pos ht) (pow2_width_le_64 ht) b

theorem pow2_toInt_twoPow_lt {w k : Nat} (h : k + 1 < w) :
    (BitVec.twoPow w k).toInt = ((2 ^ k : Nat) : Int) := by
  rw [pow2_toInt_twoPow (by omega), ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem pow2_ctz64_neg {k : Nat} (hk : k < 64) : Rust.ctz64 (-((2 ^ k : Nat) : Int)) = k := by
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hpos := Nat.two_pow_pos k
  have hq : 0 < 2 ^ (64 - k) := Nat.two_pow_pos _
  unfold Rust.ctz64 Rust.asU64
  have h1 : ((BitVec.ofInt 64 (-((2 ^ k : Nat) : Int))).toNat : Int).toNat =
      (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Int.toNat_natCast, BitVec.toNat_ofInt, Nat.sub_mul, Nat.one_mul, ← e]
    have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
    generalize 2 ^ k = m at hp hpos ⊢
    simp only [Nat.reducePow] at hp ⊢
    omega
  simp only [h1]
  have hodd : (2 ^ (64 - k) - 1) % 2 = 1 := by
    obtain ⟨n, hn⟩ : ∃ n, 64 - k = n + 1 := ⟨63 - k, by omega⟩
    rw [hn, Nat.pow_succ]
    have := Nat.two_pow_pos n
    omega
  have h0 : ((2 ^ (64 - k) - 1) * 2 ^ k == 0) = false := by
    have : 0 < 2 ^ (64 - k) - 1 := by omega
    simp only [beq_eq_false_iff_ne, ne_eq, Nat.mul_eq_zero, not_or]; omega
  rw [h0]
  simp only [Bool.false_eq_true, ite_false]
  rw [ctz64_go k _ 0 64 (fun i hi => by simp [Nat.testBit_mul_two_pow]; omega)
    (by simp [Nat.testBit_mul_two_pow, Nat.testBit_zero, hodd]) hk]
  omega

/-! ## The right-hand sides' shift sequences

Each rule's bit-level obligation, stated at a symbolic non-`i128` type in the form the
right-hand side evaluates to (`BitVec.ofInt` of the helpers' `Int` results). Proof: the
division becomes shifts (above), the exponent `k` a bit vector `s` (`k = s.toNat`), then
`bv_decide` per width. -/

theorem pow2_exists_toNat {w k : Nat} (h : k < 2 ^ w) : ∃ s : BitVec w, s.toNat = k :=
  ⟨BitVec.ofNat w k, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]⟩

theorem pow2_twoPow_beq_zero {w k : Nat} (hk : k < w) : (BitVec.twoPow w k == 0#w) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := congrArg BitVec.toNat (beq_iff_eq.1 h)
  rw [BitVec.toNat_twoPow_of_lt hk] at this
  have := Nat.two_pow_pos k
  simp_all

theorem pow2_twoPow_beq_allOnes {w k : Nat} (hk : k < w) (hw : 2 ≤ w) :
    (BitVec.twoPow w k == BitVec.allOnes w) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := congrArg BitVec.toNat (beq_iff_eq.1 h)
  rw [BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_allOnes] at this
  have h1 : 2 ^ k ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have h3 : 2 ≤ 2 ^ (w - 1) := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ w - 1 by omega); simpa using this
  omega

/-- `arithmetic.isle` 83: `udiv x (2 ^ k)` as `ushr x k`. -/
theorem pow2_udiv_seq {w k : Nat} (hk : k < w) (a : BitVec w) :
    a / BitVec.twoPow w k = Sem.ushr a (BitVec.ofInt w (k : Int)) := by
  rw [BitVec.udiv_twoPow_eq_of_lt hk, Sem.ushr, Sem.shiftAmt, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self), Nat.mod_eq_of_lt hk]

theorem pow2_u64Shl_one {k : Nat} (hk : k < 64) : Rust.u64Shl 1 (k : Int) = .ok ((2 ^ k : Nat) : Int) := by
  have h1 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have e : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by rw [Int.natCast_pow]; rfl
  unfold Rust.u64Shl
  split
  · omega
  · simp only [Int.toNat_natCast, Int.one_mul, e]
    rw [pow2_asU64_of_lt (Int.natCast_nonneg _) (by exact_mod_cast h1)]; rfl

theorem pow2_checkedSubU_two_pow {fn : String} (k : Nat) :
    Rust.checkedSubU fn ((2 ^ k : Nat) : Int) 1 = .ok ((2 ^ k - 1 : Nat) : Int) := by
  have := Nat.two_pow_pos k
  rw [pow2_checkedSubU_ok (by omega)]
  congr 1; omega

theorem pow2_decide_mask_le {k w : Nat} (hk : k < w) :
    decide (((2 ^ k - 1 : Nat) : Int) ≤ 2 ^ w - 1) = true := by
  have h1 := Nat.pow_lt_pow_right (a := 2) (by decide) hk
  have e2 : (2 : Int) ^ w - 1 = ((2 ^ w - 1 : Nat) : Int) := by
    rw [Int.ofNat_sub Nat.one_le_two_pow, Int.natCast_pow]; rfl
  rw [decide_eq_true_eq, e2]
  exact Int.ofNat_le.2 (by omega)

theorem pow2_asI64_mask {k : Nat} (hk : k < 64) :
    Rust.asI64 ((2 ^ k - 1 : Nat) : Int) = ((2 ^ k - 1 : Nat) : Int) := by
  have h1 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  apply pow2_asI64_of_lt (by omega)
  have : ((2 ^ k - 1 : Nat) : Int) < ((2 ^ 63 : Nat) : Int) := by
    have := Nat.two_pow_pos k; omega
  simpa using this

/-- `arithmetic.isle` 135: `urem x (2 ^ k)` as `band x (2 ^ k - 1)`. -/
theorem pow2_urem_seq {w k : Nat} (hk : k < w) (a : BitVec w) :
    a % BitVec.twoPow w k = Sem.binary .band a (BitVec.ofInt w ((2 ^ k - 1 : Nat) : Int)) := by
  rw [pow2_umod_twoPow hk, Sem.binary, Sem.band, BitVec.ofInt_natCast]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h2 := Nat.two_pow_pos k
  have h3 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have h4 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h1 : 1#w ≤ BitVec.twoPow w k := by
    rw [BitVec.le_def, BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]
    omega
  rw [BitVec.toNat_sub_of_le h1, BitVec.toNat_twoPow_of_lt hk, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega)]

theorem pow2_width_cases {t : Ty} (ht : t ≠ .i128) :
    t.width = 8 ∨ t.width = 16 ∨ t.width = 32 ∨ t.width = 64 := by
  cases t <;> simp_all [Ty.width]

/-- The exponent of `twoPow w k` as a bit vector `s` with `s.toNat = k`, and the bounds
`lo ≤ k`, `k + 1 < w + hi` as `BitVec` comparisons. -/
theorem pow2_toNat_lt {w : Nat} (s : BitVec w) (n : Nat) (h : s.toNat < n) (hn : n < 2 ^ w) :
    s < BitVec.ofNat w n := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h

theorem pow2_lt_toNat {w : Nat} (s : BitVec w) (n : Nat) (h : n < s.toNat) (hn : n < 2 ^ w) :
    BitVec.ofNat w n < s := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h

set_option maxHeartbeats 4000000 in
theorem pow2_sdiv_bv {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a s : BitVec w)
    (h1 : BitVec.ofNat w 0 < s) (h2 : s < BitVec.ofNat w (w - 1)) :
    (bif a.msb then -((-a) >>> s) else a >>> s) =
      Sem.sshr (Sem.binary .iadd a (Sem.ushr (Sem.sshr a (s - BitVec.ofNat w 1))
        (BitVec.ofNat w w - s))) s := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [sshr_mask, ushr_mask, Sem.binary, Sem.iadd, Nat.reduceSub] <;>
    bv_decide (config := { timeout := 120 })

/-- `arithmetic.isle` 87: `sdiv x (2 ^ k)` (`0 < k < w - 1`) as the biased shift sequence. -/
theorem pow2_sdiv_seq {t : Ty} (ht : t ≠ .i128) {k : Nat} (h1 : 0 < k) (h2 : k + 1 < t.width)
    (a : BitVec t.width) :
    a.sdiv (BitVec.twoPow t.width k) =
      Sem.sshr (Sem.binary .iadd a (Sem.ushr (Sem.sshr a (BitVec.ofInt t.width ((k : Int) - 1)))
        (BitVec.ofInt t.width ((t.width : Int) - k)))) (BitVec.ofInt t.width (k : Int)) := by
  have hp := Nat.lt_two_pow_self (n := t.width)
  rw [pow2_sdiv_twoPow h2]
  obtain ⟨s, rfl⟩ := pow2_exists_toNat (Nat.lt_trans (by omega : k < t.width) hp)
  simp only [ofInt_sub', BitVec.ofInt_natCast, BitVec.ofInt_ofNat, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, ← BitVec.ushiftRight_eq']
  exact pow2_sdiv_bv (pow2_width_cases ht) a s (pow2_lt_toNat s 0 h1 (by omega))
    (pow2_toNat_lt s _ (by omega) (by omega))

theorem pow2_toNat_neg_twoPow {w k : Nat} (hk : k < w) :
    (-(BitVec.twoPow w k)).toNat = 2 ^ w - 2 ^ k := by
  have h1 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h2 := Nat.two_pow_pos k
  rw [BitVec.toNat_neg, BitVec.toNat_twoPow_of_lt hk, Nat.mod_eq_of_lt (by omega)]

theorem pow2_neg_twoPow_beq_zero {w k : Nat} (hk : k < w) :
    (-(BitVec.twoPow w k) == 0#w) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := congrArg BitVec.toNat (beq_iff_eq.1 h)
  have h1 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  rw [pow2_toNat_neg_twoPow hk] at this
  simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
  omega

theorem pow2_neg_twoPow_beq_allOnes {w k : Nat} (hk : k < w) (h0 : 0 < k) :
    (-(BitVec.twoPow w k) == BitVec.allOnes w) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have := congrArg BitVec.toNat (beq_iff_eq.1 h)
  have h1 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h2 := Nat.one_lt_two_pow (show k ≠ 0 by omega)
  rw [pow2_toNat_neg_twoPow hk, BitVec.toNat_allOnes] at this
  omega

set_option maxHeartbeats 4000000 in
theorem pow2_sdiv_neg_bv {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a s : BitVec w)
    (h1 : BitVec.ofNat w 0 < s) (h2 : s < BitVec.ofNat w w) :
    (bif a.msb then (-a) >>> s else -(a >>> s)) =
      Sem.unary .ineg (Sem.sshr (Sem.binary .iadd a (Sem.ushr (Sem.sshr a (s - BitVec.ofNat w 1))
        (BitVec.ofNat w w - s))) s) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [sshr_mask, ushr_mask, Sem.binary, Sem.iadd, Sem.unary, Sem.ineg,
      Nat.reduceSub] <;>
    bv_decide (config := { timeout := 120 })

/-- `arithmetic.isle` 102: `sdiv x (-2 ^ k)` (`0 < k < w`) as the negated biased shift sequence. -/
theorem pow2_sdiv_neg_seq {t : Ty} (ht : t ≠ .i128) {k : Nat} (h1 : 0 < k) (h2 : k < t.width)
    (a : BitVec t.width) :
    a.sdiv (-BitVec.twoPow t.width k) =
      Sem.unary .ineg (Sem.sshr (Sem.binary .iadd a (Sem.ushr (Sem.sshr a
        (BitVec.ofInt t.width ((k : Int) - 1))) (BitVec.ofInt t.width ((t.width : Int) - k))))
        (BitVec.ofInt t.width (k : Int))) := by
  have hp := Nat.lt_two_pow_self (n := t.width)
  rw [pow2_sdiv_neg_twoPow h2]
  obtain ⟨s, rfl⟩ := pow2_exists_toNat (Nat.lt_trans h2 hp)
  simp only [ofInt_sub', BitVec.ofInt_natCast, BitVec.ofInt_ofNat, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, ← BitVec.ushiftRight_eq']
  exact pow2_sdiv_neg_bv (pow2_width_cases ht) a s (pow2_lt_toNat s 0 h1 (by omega))
    (pow2_toNat_lt s _ h2 hp)

/-! ## `srem` by `± 2 ^ k`: the mask `iconst_s (i64_wrapping_neg (i64_shl 1 k))` -/

theorem pow2_asI64_of_range {a : Int} (h1 : -2 ^ 63 ≤ a) (h2 : a < 2 ^ 63) : Rust.asI64 a = a := by
  simp only [Rust.asI64, BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le_mul_two <;> simp only [Nat.reducePow, Int.reducePow] at * <;> omega

theorem pow2_i64Shl_one {k : Nat} (hk : k < 64) :
    Rust.i64Shl 1 (k : Int) = .ok (Rust.asI64 ((2 ^ k : Nat) : Int)) := by
  unfold Rust.i64Shl
  split
  · omega
  · simp only [Int.toNat_natCast, Int.one_mul, pow2_int_two_pow]; rfl

theorem pow2_asI64_neg_asI64 {k : Nat} (hk : k < 64) :
    Rust.asI64 (-(Rust.asI64 ((2 ^ k : Nat) : Int))) = -((2 ^ k : Nat) : Int) := by
  by_cases h : k < 63
  · have h1 : 2 ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) h
    have h2 : ((2 ^ k : Nat) : Int) < 2 ^ 63 := by
      rw [pow2_int_two_pow]; exact_mod_cast h1
    have h0 : (0 : Int) ≤ ((2 ^ k : Nat) : Int) := Int.natCast_nonneg _
    rw [pow2_asI64_of_lt h0 h2, pow2_asI64_of_range (by omega) (by omega)]
  · obtain rfl : k = 63 := by omega
    decide

theorem pow2_ofInt_asI64 {w : Nat} (hw : w ≤ 64) (z : Int) :
    BitVec.ofInt w (Rust.asI64 z) = BitVec.ofInt w z := by
  rw [Rust.asI64, ofInt_toInt_signExtend, BitVec.signExtend_eq_setWidth_of_le _ hw]
  rcases Nat.lt_or_ge w 64 with h | h
  · rw [ofInt_eq_setWidth h]
  · obtain rfl : w = 64 := by omega
    rw [BitVec.setWidth_eq]

theorem pow2_ofInt_mask_neg {w k : Nat} (hk : k < w) :
    BitVec.ofInt w ((2 ^ w - 2 ^ k : Nat) : Int) = -BitVec.twoPow w k := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h2 := Nat.two_pow_pos k
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, pow2_toNat_neg_twoPow hk, Nat.mod_eq_of_lt (by omega)]

theorem pow2_band64_neg {w k : Nat} (hk : k < w) (hw : w ≤ 64) :
    Rust.band64 (Rust.asU64 (-((2 ^ k : Nat) : Int))) (2 ^ w - 1) = ((2 ^ w - 2 ^ k : Nat) : Int) := by
  have h1 : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have h2 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - w) * 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega
  have hq : 0 < 2 ^ (64 - w) := Nat.two_pow_pos _
  have hu : Rust.asU64 (-((2 ^ k : Nat) : Int)) = ((2 ^ 64 - 2 ^ k : Nat) : Int) := by
    have h3 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 := Nat.two_pow_pos k
    have h5 : 2 ^ k ≤ 2 ^ 64 := by omega
    rw [Int.ofNat_sub h5]
    generalize 2 ^ k = n at h3 h4 h5 ⊢
    rw [pow2_asU64_cases (by simp only [Nat.reducePow, Int.reducePow] at *; omega)
      (by simp only [Nat.reducePow, Int.reducePow] at *; omega)]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    simp only [Nat.reducePow, Int.reducePow] at *; omega
  have hm : (2 : Int) ^ w - 1 = ((2 ^ w - 1 : Nat) : Int) := by
    rw [pow2_int_two_pow]; have := Nat.two_pow_pos w; omega
  rw [hu, hm, Rust.band64, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.toNat_and,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.two_pow_pos k; omega),
    Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod]
  congr 1
  rw [e]
  generalize 2 ^ w = m at h1 h2 hq ⊢
  generalize 2 ^ (64 - w) = q at hq ⊢
  have h0 := Nat.two_pow_pos k
  generalize 2 ^ k = n at h0 h1 ⊢
  have : q * m - n = (q - 1) * m + (m - n) := by
    rw [Nat.sub_mul, Nat.one_mul]
    have : m ≤ q * m := Nat.le_mul_of_pos_left m hq
    omega
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem pow2_sext_neg_mask {w k : Nat} (hk : k < w) (hw : w ≤ 64) :
    Rust.sext w (Rust.asI64 ((2 ^ w - 2 ^ k : Nat) : Int)) = -((2 ^ k : Nat) : Int) := by
  unfold Rust.sext
  split
  · obtain rfl : w = 64 := by omega
    rw [Rust.asI64, pow2_ofInt_mask_neg hk, pow2_toInt_neg_twoPow hk]
  · rw [pow2_ofInt_asI64 hw, pow2_ofInt_mask_neg hk, pow2_toInt_neg_twoPow hk]

/-- **`imm64_power_of_two`** of a presented immediate: `some k` exactly when the bits are
`2 ^ k` with `k < 63` (the `i64` is non-negative). -/
theorem pow2_imm64PowerOfTwo_ty {t : Ty} (ht : t ≠ .i128) (b : BitVec t.width) (e : Int) :
    Rust.imm64PowerOfTwo (imm64OfBits b) = some e ↔
      ∃ k, k < t.width ∧ k < 63 ∧ b = BitVec.twoPow t.width k ∧ e = k := by
  have hw := pow2_width_le_64 ht
  unfold Rust.imm64PowerOfTwo
  by_cases hb : b.toNat < 2 ^ 63
  · rw [imm64OfBits_of_lt b hb]
    constructor
    · intro h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨k, hk, rfl⟩ := (pow2_isPow2_toNat_iff b).1 hc.2
        rw [BitVec.toNat_twoPow_of_lt hk] at h hb
        rw [pow2_ctz64 (by omega)] at h
        exact ⟨k, hk, (Nat.pow_lt_pow_iff_right (by decide)).1 hb, rfl,
          (Option.some.inj h).symm⟩
      · simp at h
    · rintro ⟨k, hk, hk63, rfl, rfl⟩
      have hp : Rust.isPow2 ((BitVec.twoPow t.width k).toNat : Int) = true :=
        (pow2_isPow2_toNat_iff _).2 ⟨k, hk, rfl⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Int.natCast_nonneg _, hp⟩)), BitVec.toNat_twoPow_of_lt hk,
        pow2_ctz64 (by omega)]
  · have hneg : imm64OfBits b < 0 := by
      have hlt := b.isLt
      have h2 : 2 ^ t.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
      rw [imm64OfBits_eq hw, BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.reducePow] at *
      split <;> omega
    constructor
    · intro h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        omega
      · simp at h
    · rintro ⟨k, hk, hk63, rfl, rfl⟩
      exfalso; apply hb
      rw [BitVec.toNat_twoPow_of_lt hk]
      exact Nat.pow_lt_pow_right (by decide) hk63

/-- `arithmetic.isle` 181: `imul x (2 ^ k)` as `ishl x k`. -/
theorem pow2_imul_seq {w k : Nat} (hk : k < w) (a : BitVec w) :
    a * BitVec.twoPow w k = Sem.ishl a (BitVec.ofInt w (k : Int)) := by
  rw [BitVec.mul_twoPow_eq_shiftLeft, Sem.ishl, Sem.shiftAmt, BitVec.ofInt_natCast,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self), Nat.mod_eq_of_lt hk]

theorem pow2_twoPow_toNat {w : Nat} (s : BitVec w) : BitVec.twoPow w s.toNat = 1#w <<< s := rfl

set_option maxHeartbeats 4000000 in
theorem pow2_srem_bv {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (a s : BitVec w)
    (h1 : BitVec.ofNat w 0 < s) (h2 : s < BitVec.ofNat w w) :
    (bif a.msb then -((-a) &&& (1#w <<< s - 1#w)) else a &&& (1#w <<< s - 1#w)) =
      Sem.binary .isub a (Sem.binary .band (Sem.binary .iadd a (Sem.ushr (Sem.sshr a
        (s - BitVec.ofNat w 1)) (BitVec.ofNat w w - s))) (-(1#w <<< s))) := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [sshr_mask, ushr_mask, Sem.binary, Sem.iadd, Sem.isub, Sem.band,
      Nat.reduceSub] <;>
    bv_decide (config := { timeout := 120 })

theorem pow2_srem_seq {t : Ty} (ht : t ≠ .i128) {k : Nat} (h1 : 0 < k) (h2 : k < t.width)
    (a : BitVec t.width) :
    (bif a.msb then -((-a) &&& (BitVec.twoPow t.width k - 1#t.width))
      else a &&& (BitVec.twoPow t.width k - 1#t.width)) =
      Sem.binary .isub a (Sem.binary .band (Sem.binary .iadd a (Sem.ushr (Sem.sshr a
        (BitVec.ofInt t.width ((k : Int) - 1))) (BitVec.ofInt t.width ((t.width : Int) - k))))
        (BitVec.ofInt t.width (Rust.asI64 ((2 ^ t.width - 2 ^ k : Nat) : Int)))) := by
  have hp := Nat.lt_two_pow_self (n := t.width)
  rw [pow2_ofInt_asI64 (pow2_width_le_64 ht), pow2_ofInt_mask_neg h2]
  obtain ⟨s, rfl⟩ := pow2_exists_toNat (Nat.lt_trans h2 hp)
  simp only [ofInt_sub', BitVec.ofInt_natCast, BitVec.ofInt_ofNat, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, ← BitVec.ushiftRight_eq', pow2_twoPow_toNat]
  exact pow2_srem_bv (pow2_width_cases ht) a s (pow2_lt_toNat s 0 h1 (by omega))
    (pow2_toNat_lt s _ h2 hp)

/-- `arithmetic.isle` 142, positive divisor `2 ^ k` (`0 < k < w - 1`). -/
theorem pow2_srem_pos_seq {t : Ty} (ht : t ≠ .i128) {k : Nat} (h1 : 0 < k) (h2 : k + 1 < t.width)
    (a : BitVec t.width) :
    a.srem (BitVec.twoPow t.width k) =
      Sem.binary .isub a (Sem.binary .band (Sem.binary .iadd a (Sem.ushr (Sem.sshr a
        (BitVec.ofInt t.width ((k : Int) - 1))) (BitVec.ofInt t.width ((t.width : Int) - k))))
        (BitVec.ofInt t.width (Rust.asI64 ((2 ^ t.width - 2 ^ k : Nat) : Int)))) := by
  rw [pow2_srem_twoPow h2]; exact pow2_srem_seq ht h1 (by omega) a

/-- `arithmetic.isle` 142, negative divisor `-2 ^ k` (`0 < k < w`). -/
theorem pow2_srem_neg_seq {t : Ty} (ht : t ≠ .i128) {k : Nat} (h1 : 0 < k) (h2 : k < t.width)
    (a : BitVec t.width) :
    a.srem (-BitVec.twoPow t.width k) =
      Sem.binary .isub a (Sem.binary .band (Sem.binary .iadd a (Sem.ushr (Sem.sshr a
        (BitVec.ofInt t.width ((k : Int) - 1))) (BitVec.ofInt t.width ((t.width : Int) - k))))
        (BitVec.ofInt t.width (Rust.asI64 ((2 ^ t.width - 2 ^ k : Nat) : Int)))) := by
  rw [pow2_srem_neg_twoPow h2]; exact pow2_srem_seq ht h1 h2 a

theorem pow2_select_beq_zero {v w k₁ k₂ : Nat} (h₁ : k₁ < w) (h₂ : k₂ < w) (c : BitVec v) :
    (!(Sem.select c (BitVec.twoPow w k₁) (BitVec.twoPow w k₂) == 0#w)) = true := by
  unfold Sem.select
  split <;> simp only [pow2_twoPow_beq_zero h₁, pow2_twoPow_beq_zero h₂, Bool.not_false]

/-- `skeleton.isle` 80: `udiv y (select x (2 ^ n) (2 ^ m))` as `ushr y (select x n m)`. -/
theorem pow2_udiv_select_seq {v w k₁ k₂ : Nat} (h₁ : k₁ < w) (h₂ : k₂ < w) (c : BitVec v)
    (a : BitVec w) :
    a / Sem.select c (BitVec.twoPow w k₁) (BitVec.twoPow w k₂) =
      Sem.ushr a (Sem.select c (BitVec.ofInt w (k₁ : Int)) (BitVec.ofInt w (k₂ : Int))) := by
  unfold Sem.select
  split
  · exact pow2_udiv_seq h₁ a
  · exact pow2_udiv_seq h₂ a

/-- `arithmetic.isle` 181 (a `simplify` rule): `imul x (2 ^ k)` as `ishl x (imm64 k)`. -/
theorem pow2_imul_ishl {w k : Nat} (hk : k < w) (hk63 : k < 63) (a : BitVec w) :
    Sem.binary .imul a (BitVec.twoPow w k) = Sem.ishl a (BitVec.ofInt w (Rust.asI64 (k : Int))) := by
  have h : (k : Int) < 2 ^ 63 := by
    have : k < 2 ^ 63 := Nat.lt_trans hk63 (Nat.lt_two_pow_self)
    rw [pow2_int_two_pow]; exact_mod_cast this
  rw [pow2_asI64_of_lt (Int.natCast_nonneg _) h]
  exact pow2_imul_seq hk a

open Lean Meta Elab Tactic in
/-- `pow2_neg_goal`: succeeds iff the goal mentions a negated power of two `-twoPow w k` (picks
the bit-level lemma syntactically: a failed `exact` would unfold the bit-vector operations). -/
elab "pow2_neg_goal" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  unless (t.find? fun e => e.isAppOfArity ``Neg.neg 3 &&
      (e.getArg! 2).isAppOfArity ``BitVec.twoPow 2).isSome do
    throwError "pow2_neg_goal: no negated power of two"

/-- The left-hand side's power-of-two facts in the normal form `b = BitVec.twoPow w k`. -/
macro "pow2_lhs" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, pow2_isPow2_toNat_ty,
    pow2_isPow2_pos_ty, pow2_isPow2_neg_ty, pow2_imm64PowerOfTwo_ty] at *
  opt_destruct
  all_goals subst_vars))

theorem pow2_two_pow_ne_one (k : Nat) : (((2 ^ k : Nat) : Int) ≠ 1) ↔ 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp
  · have := Nat.one_lt_two_pow (show k ≠ 0 by omega)
    simp only [h, iff_true]
    generalize 2 ^ k = m at this ⊢
    omega

theorem pow2_neg_two_pow_ne_neg_one (k : Nat) : (-((2 ^ k : Nat) : Int) ≠ -1) ↔ 0 < k := by
  rw [← pow2_two_pow_ne_one]; omega

theorem pow2_neg_two_pow_ne_one (k : Nat) : (-((2 ^ k : Nat) : Int) ≠ 1) ↔ True := by
  have := Nat.two_pow_pos k
  generalize 2 ^ k = m at this ⊢
  simp only [iff_true]; omega

theorem pow2_two_pow_ne_neg_one (k : Nat) : (((2 ^ k : Nat) : Int) ≠ -1) ↔ True := by
  have := Nat.two_pow_pos k
  generalize 2 ^ k = m at this ⊢
  simp only [iff_true]; omega

open Lean Meta Elab Tactic in
/-- `pow2_facts`: the if-let facts (`(decide (…) == true) = true`, `((d != -1) == true) = true`,
left by `skel_iflets`) as linear facts for `omega`, hypothesis by hypothesis (a `simp … at *`
would also rewrite the widths inside dependent types). -/
elab "pow2_facts" : tactic => withMainContext do
  for d in ← getLCtx do
    if (← getGoals).isEmpty then return
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless (ty.find? (fun e => e.isConstOf ``Decidable.decide || e.isConstOf ``BEq.beq ||
      e.isConstOf ``bne || e.isConstOf ``BitVec.toInt)).isSome do continue
    if (ty.find? (·.isConstOf ``Except)).isSome then continue
    if (ty.find? (·.isConstOf ``StateT.run)).isSome then continue
    let hn ← mkFreshUserName `hf
    let g ← (← getMainGoal).rename d.fvarId hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    try
      evalTactic (← `(tactic| simp (disch := first | assumption | omega) only [beq_true,
        beq_false, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true, bne_iff_ne,
        pow2_natCast_gt_one, ge_iff_le, gt_iff_lt, pow2_toInt_twoPow_lt, pow2_toInt_neg_twoPow,
        pow2_two_pow_ne_one, pow2_neg_two_pow_ne_neg_one, pow2_neg_two_pow_ne_one,
        pow2_two_pow_ne_neg_one, Bool.false_eq_true] at $hi:ident))
    catch _ => pure ()

/-- Width facts of a non-`i128` type, for `omega` (`2 ^ t.width` and `2 ^ (t.width - 1)` are atoms
to it). -/
theorem pow2_width_facts {t : Ty} (ht : t ≠ .i128) :
    8 ≤ t.width ∧ t.width ≤ 64 ∧ (t.width : Int) ≤ 2 ^ (t.width - 1) ∧
      (2 : Int) ^ t.width = 2 * 2 ^ (t.width - 1) ∧ (2 : Int) ^ t.width ≤ 18446744073709551616 ∧
      (2 : Int) ^ (t.width - 1) ≤ 9223372036854775808 := by
  cases t <;> simp_all [Ty.width] <;> decide

open Lean Meta Elab Tactic in
/-- `pow2_wfacts`: `pow2_width_facts` for the type with a hypothesis `t ≠ .i128`. -/
elab "pow2_wfacts" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Ne 3 && (ty.getArg! 2).isConstOf ``Clif.Ty.i128 && (ty.getArg! 1).isFVar then
      let h ← Term.exprToSyntax d.toExpr
      evalTactic (← `(tactic| obtain ⟨_, _, _, _, _, _⟩ := pow2_width_facts $h))
      return
  throwError "pow2_wfacts: no type with a `≠ .i128` hypothesis"

/-- Side conditions of the helper lemmas: a hypothesis, or linear arithmetic (with the width
facts of `pow2_wfacts`, or once the widths are numerals). -/
macro "pow2_disch" : tactic => `(tactic| first
  | assumption
  | omega
  | (simp only [Ty.width, Nat.reducePow, Nat.reduceSub, Int.reducePow]; omega))

/-- `opt_norm` with `pow2_disch` and the power-of-two helper lemmas. -/
syntax "pow2_norm " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| pow2_norm $h:ident) => `(tactic| pow2_norm $h [])
  | `(tactic| pow2_norm $h:ident [$ts,*]) => `(tactic|
      repeat (first
        | simp (disch := pow2_disch) only [opt_data, $ts,*] at $h:ident
        | simp (disch := pow2_disch) only [opt_monad, opt_imm, BitVec.toNat_twoPow_of_lt,
            pow2_ctz64, pow2_u64Ilog2, pow2_checkedSubU_ok, pow2_decide_le_true, beq_self_eq_true,
            pow2_asU64_of_lt, pow2_asI64_of_lt, pow2_band64_mask, pow2_sext_of_lt, pow2_u64Shl_one,
            pow2_checkedSubU_two_pow, pow2_decide_mask_le, pow2_asI64_mask, pow2_toInt_twoPow_lt,
            pow2_toInt_neg_twoPow, pow2_ctz64_neg, pow2_i64Shl_one, pow2_asI64_neg_asI64,
            pow2_band64_neg, pow2_sext_neg_mask, $ts,*] at $h:ident))

/-- `opt_eval` with `pow2_norm`. -/
syntax "pow2_eval " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
macro_rules
  | `(tactic| pow2_eval $h:ident) => `(tactic| pow2_eval $h [])
  | `(tactic| pow2_eval $h:ident [$ts,*]) => `(tactic|
      (pow2_norm $h [$ts,*]; repeat (opt_unfold $h; pow2_norm $h [$ts,*])))

set_option hygiene false in
/-- `skel_rule_iflets` with `pow2_eval`. -/
syntax "pow2_iflets" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| pow2_iflets) => `(tactic| pow2_iflets [])
  | `(tactic| pow2_iflets [$ts,*]) => `(tactic| (
  pow2_eval hil [$ts,*]
  repeat' ((first | opt_split_ite hil | split at hil) <;> try pow2_eval hil [$ts,*])
  all_goals (try (simp at hil; done))
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hil
    obtain ⟨rfl, rfl, rfl⟩ := hil
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at henv2)
  all_goals subst henv2))

set_option hygiene false in
/-- `skel_rhs` with `pow2_eval`; failed helper calls (`Except.error`) are dropped. -/
syntax "pow2_rhs" ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| pow2_rhs) => `(tactic| pow2_rhs [])
  | `(tactic| pow2_rhs [$ts,*]) => `(tactic| (
  pow2_eval hev [$ts,*]
  repeat' (split at hev <;> try pow2_norm hev [$ts,*])
  all_goals (try (simp only [reduceCtorEq] at hev; done))
  all_goals (try simp only [Option.map_eq_some_iff, Option.map_eq_none_iff] at *)
  opt_destruct
  all_goals subst_vars
  all_goals (
    simp only [Except.ok.injEq, Prod.mk.injEq] at hev
    obtain ⟨rfl, rfl, rfl⟩ := hev
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw <;>
    subst hw)
  all_goals opt_types
  all_goals (try (exfalso; omega))))

set_option hygiene false in
/-- Phase 4 for a `div` replaced by a value: no trap (`divOk`: the divisor `± 2 ^ k` is neither
`0` nor `-1`), and the value, closed by the bit-level lemma `e` (applied to the made node's
value). -/
syntax "pow2_div_fin " tactic : tactic
set_option hygiene false in
macro_rules
  | `(tactic| pow2_div_fin $e:tactic) => `(tactic| (
  apply skel_div_rwv (hle4 _ _ (by opt_den)) (hle4 _ _ (by opt_den))
  intro a b ha hb
  opt_destruct
  all_goals subst_vars
  refine ⟨?_, ?_⟩
  · simp (disch := pow2_disch) only [divOk, pow2_twoPow_beq_zero, pow2_twoPow_beq_allOnes,
      pow2_neg_twoPow_beq_zero, pow2_neg_twoPow_beq_allOnes, pow2_select_beq_zero,
      Bool.not_false, Bool.and_false, Bool.and_true]
  · simp only [divVal]
    try dsimp only
    apply hle4
    apply GraphOk.make_val hG (by opt_P)
    opt_node
    all_goals (apply val_congr; $e)))

set_option hygiene false in
/-- The whole template for a power-of-two `div`/`rem` skeleton rule. -/
syntax "pow2_auto_div " ident " using " tactic : tactic
set_option hygiene false in
macro_rules
  | `(tactic| pow2_auto_div $r using $e:tactic) => `(tactic| (
  skel_intro $r
  rule_lhs hG
  skel_reads
  rule_lhs hG
  all_goals pow2_lhs
  all_goals pow2_wfacts
  all_goals (first | rule_no_iflets | (pow2_iflets; skel_iflets))
  all_goals pow2_facts
  all_goals pow2_lhs
  all_goals pow2_facts
  all_goals pow2_rhs
  all_goals skel_good
  all_goals pow2_div_fin $e))

set_option hygiene false in
/-- The template for a `simplify` rule matching a power-of-two `iconst` (`imm64_power_of_two`):
the left-hand side in the normal form, the right-hand side, then the made node's value by the
bit-level lemma (tactic `e`). -/
syntax "pow2_auto_simp " ident " using " tactic : tactic
set_option hygiene false in
macro_rules
  | `(tactic| pow2_auto_simp $r using $e:tactic) => `(tactic| (
  rule_intro $r
  rule_no_iflets
  rule_lhs hG
  all_goals pow2_lhs
  all_goals rule_rhs
  all_goals (
    try dsimp only
    apply GraphOk.make_val hG (by opt_P)
    opt_node
    all_goals (apply val_congr; $e))))

end Opt.Proof

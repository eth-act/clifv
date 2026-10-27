import FVFloatSpec.Basic

/-!
# Addition, subtraction, multiplication and FMA: `FV/Float` against FloatLib

`IEEE.add`, `IEEE.sub`, `IEEE.mul` and `IEEE.mulAdd` (`FPAdd`, `FPSub`, `FPMul`, `FPMulAdd`) in
every `FPCR` rounding mode are FloatLib's `addWithRounding`, `subWithRounding`,
`mulWithRounding` and `fmaWithRounding` on the same bits. `sub` and `mulAdd` differ from FloatLib
only in NaN results (FloatLib's `sub` negates `y`'s NaN; `FPMulAdd` checks `0 * ∞` before a quiet
NaN addend), so their main theorems keep the Arm NaN selection and defer to FloatLib otherwise.
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

variable {f : Fmt} (h : FmtOk f)

/-! ## Bit fields -/

theorem pack_toNat (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F) :
    (pack f s b fr).toNat = (if s then 2 ^ f.E * 2 ^ f.F else 0) + b * 2 ^ f.F + fr := by
  have h1 : b * 2 ^ f.F + fr < 2 ^ f.E * 2 ^ f.F := by
    have := Nat.mul_le_mul_right (2 ^ f.F) (show b + 1 ≤ 2 ^ f.E by omega)
    rw [Nat.add_mul] at this; omega
  have h2 : (2 : Nat) ^ (1 + f.E + f.F) = 2 * (2 ^ f.E * 2 ^ f.F) := by
    rw [Nat.pow_add, Nat.pow_add]; ring
  simp only [pack, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ (f.E + f.F) = 2 ^ f.E * 2 ^ f.F from Nat.pow_add _ _ _, h2]
  rw [Nat.mod_eq_of_lt (by cases s <;> simp <;> omega)]

private theorem fields_pack (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F) :
    signOf f (pack f s b fr) = s ∧ expOf f (pack f s b fr) = b ∧ fracOf f (pack f s b fr) = fr := by
  have h1 : b * 2 ^ f.F + fr < 2 ^ f.E * 2 ^ f.F := by
    have := Nat.mul_le_mul_right (2 ^ f.F) (show b + 1 ≤ 2 ^ f.E by omega)
    rw [Nat.add_mul] at this; omega
  have hP : 0 < 2 ^ f.F := by positivity
  simp only [signOf, expOf, fracOf, pack_toNat s b fr hb hfr, Nat.pow_add]
  refine ⟨?_, ?_, ?_⟩
  · cases s <;> simp <;> omega
  · have : (if s then 2 ^ f.E * 2 ^ f.F else 0) + b * 2 ^ f.F + fr =
        fr + 2 ^ f.F * ((if s then 2 ^ f.E else 0) + b) := by cases s <;> simp <;> ring
    rw [this, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hfr, Nat.zero_add]
    cases s <;> simp [Nat.mod_eq_of_lt hb]
  · have : (if s then 2 ^ f.E * 2 ^ f.F else 0) + b * 2 ^ f.F + fr =
        fr + 2 ^ f.F * ((if s then 2 ^ f.E else 0) + b) := by cases s <;> simp <;> ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfr]

private theorem expOf_lt (x : Bits f) : expOf f x < 2 ^ f.E := Nat.mod_lt _ (by positivity)
private theorem fracOf_lt (x : Bits f) : fracOf f x < 2 ^ f.F := Nat.mod_lt _ (by positivity)

theorem bits_eq_pack (x : Bits f) : x = pack f (signOf f x) (expOf f x) (fracOf f x) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat _ _ _ (expOf_lt x) (fracOf_lt x)]
  have hx := x.isLt
  have hP : 0 < 2 ^ f.F := by positivity
  have hQ : 0 < 2 ^ f.E := by positivity
  simp only [signOf, expOf, fracOf, Nat.pow_add] at *
  generalize x.toNat = n at *
  generalize 2 ^ f.F = P at *
  generalize 2 ^ f.E = Q at *
  have e1 := Nat.div_add_mod n P
  have e2 := Nat.div_add_mod (n / P) Q
  have e3 : n / P / Q < 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]; linarith
  have e4 := Nat.mod_lt n hP
  have e5 := Nat.mod_lt (n / P) hQ
  generalize n / P / Q = a at *
  generalize n / P % Q = b at *
  generalize n % P = c at *
  generalize n / P = d at *
  subst e2
  have h6 : P * (b + 1) ≤ P * Q := Nat.mul_le_mul_left P e5
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
  · have : ¬ Q * P ≤ n := by nlinarith
    simp [this]; nlinarith
  · have : Q * P ≤ n := by nlinarith
    simp [this]; nlinarith

private theorem typeOf_inf (x : Bits f) (hx : typeOf f x = .infinity) : x = infinity f (signOf f x) := by
  have : expOf f x = f.expOnes ∧ fracOf f x = 0 := by
    unfold typeOf unpack at hx
    dsimp only at hx
    split_ifs at hx; simp_all
  rw [bits_eq_pack x]
  simp only [infinity]
  rw [(fields_pack _ _ _ (expOf_lt x) (fracOf_lt x)).1, this.1, this.2]

private theorem truncShift_two_mul (m s : Nat) (hs : 0 < s) :
    truncShift (2 * m) (s + 1) false = truncShift m s false := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hp : (2 : Nat) ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by rw [Nat.pow_succ]; ring
  have hq : (2 : Nat) ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; ring
  have hr : 2 * m % (2 * 2 ^ (t + 1)) = 2 * (m % 2 ^ (t + 1)) := Nat.mul_mod_mul_left _ _ _
  have hd : 2 * m / (2 * 2 ^ (t + 1)) = m / 2 ^ (t + 1) := Nat.mul_div_mul_left _ _ (by omega)
  simp only [truncShift, Nat.add_sub_cancel, hp, hr, hd]
  rw [hq] at *
  simp only at *
  congr 1
  have := Nat.mod_lt m (show 0 < 2 * 2 ^ t by positivity)
  by_cases h0 : m % (2 * 2 ^ t) = 0 <;> simp [h0]

theorem round_two_mul (rm : RMode) (s : Bool) (m : Nat) (e : Int) :
    IEEE.round f rm s (2 * m) (e - 1) = IEEE.round f rm s m e := by
  by_cases hm : m = 0
  · simp [IEEE.round, hm]
  have hlog := Nat.log2_two_mul hm
  have hex : ((2 * m).log2 : Int) + (e - 1) = (m.log2 : Int) + e := by rw [hlog]; push_cast; ring
  have key : ∀ ulp : Int,
      (if ulp - (e - 1) ≤ 0 then (2 * m * 2 ^ (-(ulp - (e - 1))).toNat, Err.exact)
        else truncShift (2 * m) (ulp - (e - 1)).toNat false) =
      (if ulp - e ≤ 0 then (m * 2 ^ (-(ulp - e)).toNat, Err.exact)
        else truncShift m (ulp - e).toNat false) := by
    intro ulp
    by_cases h1 : ulp - e ≤ 0
    · by_cases h2 : ulp - (e - 1) ≤ 0
      · rw [if_pos h2, if_pos h1]
        have : (-(ulp - e)).toNat = (-(ulp - (e - 1))).toNat + 1 := by omega
        rw [this, Nat.pow_succ]; congr 1; ring
      · rw [if_neg h2, if_pos h1]
        have h3 : (ulp - (e - 1)).toNat = 1 := by omega
        have h4 : (-(ulp - e)).toNat = 0 := by omega
        rw [h3, h4]; simp [truncShift]
    · have h2 : ¬ ulp - (e - 1) ≤ 0 := by omega
      rw [if_neg h2, if_neg h1]
      have : (ulp - (e - 1)).toNat = (ulp - e).toNat + 1 := by omega
      rw [this, truncShift_two_mul _ _ (by omega)]
  have hm2 : 2 * m ≠ 0 := by omega
  unfold IEEE.round
  simp only [hm, hm2, if_false, hex, Bool.false_eq_true]
  rw [key]

theorem round_scale (rm : RMode) (s : Bool) (m k : Nat) (e : Int) :
    IEEE.round f rm s (m * 2 ^ k) (e - k) = IEEE.round f rm s m e := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := by rw [Nat.pow_succ]; ring
    rw [this, show e - ((k + 1 : Nat) : Int) = (e - k) - 1 by push_cast; ring, round_two_mul, ih]

private theorem round_zero_mant (rm : RMode) (s : Bool) (e : Int) : IEEE.round f rm s 0 e = zero f s := by
  simp [IEEE.round]

theorem ofM_round_zero (rm : Mode) (d : FloatLib.Numerics.Dyadic) (hd : d.significand = 0) :
    ofM f h (Model.roundDyadicWithRounding (fl f h) rm d) = zero f d.negative := by
  obtain ⟨s, m, e⟩ := d
  simp only at hd; subst hd
  rw [← round_eq h, round_zero_mant]

private theorem roundSum_signed (rm : RMode) (s : Bool) (n : Nat) (e : Int) (hn : n ≠ 0) :
    roundSum f rm (signed s n) e = IEEE.round f rm s n e := by
  have := Nat.pos_of_ne_zero hn
  have h0 : ¬ ((n : Int) < 0) := by omega
  cases s <;> simp [roundSum, signed, hn, this, h0]

private theorem ofM_zeroForExactSum (rm : Mode) (s1 s2 : Bool) :
    ofM f h (Model.zeroForExactSum (fl f h) rm s1 s2) =
      zero f (if rm = .towardNegativeInfinity then s1 || s2 else s1 && s2) := by
  cases rm <;> simp [Model.zeroForExactSum, ofM_zero]

private theorem add_core (rm : Mode) (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    (if m1 = 0 ∧ m2 = 0 ∧ s1 = s2 then zero f s1
      else roundSum f rm.asl (addExact s1 m1 e1 s2 m2 e2).1 (addExact s1 m1 e1 s2 m2 e2).2) =
    ofM f h (if (Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩).significand = 0 then
        Model.zeroForExactSum (fl f h) rm s1 s2
      else Model.roundDyadicWithRounding (fl f h) rm (Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩)) := by
  by_cases h1 : m1 = 0 <;> by_cases h2 : m2 = 0
  · subst h1; subst h2
    cases rm <;> cases s1 <;> cases s2 <;>
      simp [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields,
        addExact, signed, roundSum, Model.zeroForExactSum, ofM_zero,
        Model.IEEERoundingMode.asl]
  · subst h1
    have hD : Model.addDyadic ⟨s1, 0, e1⟩ ⟨s2, m2, e2⟩ = ⟨s2, m2, e2⟩ := by
      simp [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields, h2]
    have hA : addExact s1 0 e1 s2 m2 e2 =
        (signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat), Min.min e1 e2) := by
      cases s1 <;> simp [addExact, signed]
    have hk : e2 - ((e2 - Min.min e1 e2).toNat : Int) = Min.min e1 e2 := by omega
    have hp : m2 * 2 ^ (e2 - Min.min e1 e2).toNat ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.pos_of_ne_zero h2) (by positivity))
    rw [hD, if_neg h2, if_neg (by simp [h2]), hA, roundSum_signed _ _ _ _ hp]
    have hs := round_scale (f := f) rm.asl s2 m2 (e2 - Min.min e1 e2).toNat e2
    rw [hk] at hs
    dsimp only
    rw [hs, round_eq h]
  · subst h2
    have hD : Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, 0, e2⟩ = ⟨s1, m1, e1⟩ := by
      simp [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields, h1]
    have hA : addExact s1 m1 e1 s2 0 e2 =
        (signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat), Min.min e1 e2) := by
      cases s2 <;> simp [addExact, signed]
    have hk : e1 - ((e1 - Min.min e1 e2).toNat : Int) = Min.min e1 e2 := by omega
    have hp : m1 * 2 ^ (e1 - Min.min e1 e2).toNat ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.pos_of_ne_zero h1) (by positivity))
    rw [hD, if_neg h1, if_neg (by simp [h1]), hA, roundSum_signed _ _ _ _ hp]
    have hs := round_scale (f := f) rm.asl s1 m1 (e1 - Min.min e1 e2).toNat e1
    rw [hk] at hs
    dsimp only
    rw [hs, round_eq h]
  · have hD : Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩ =
        (if signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat) +
              signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat) = 0 then ⟨s1 && s2, 0, 0⟩
         else ⟨decide (signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat) +
              signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat) < 0),
            (signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat) +
              signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat)).natAbs, Min.min e1 e2⟩) := by
      by_cases hle : e1 ≤ e2
      · have : Min.min e1 e2 = e1 := min_eq_left hle
        simp [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields,
          h1, h2, hle, signed, Nat.shiftLeft_eq]
      · have : Min.min e1 e2 = e2 := min_eq_right (by omega)
        simp [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields,
          h1, h2, hle, this, signed, Nat.shiftLeft_eq]
    have hA : addExact s1 m1 e1 s2 m2 e2 =
        (signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat) +
          signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat), Min.min e1 e2) := rfl
    rw [hD, if_neg (by simp [h1]), hA]
    dsimp only
    generalize hS : signed s1 (m1 * 2 ^ (e1 - Min.min e1 e2).toNat) +
      signed s2 (m2 * 2 ^ (e2 - Min.min e1 e2).toNat) = S
    by_cases hS0 : S = 0
    · subst hS0
      have hne : s1 ≠ s2 := by
        rintro rfl
        have p1 : 0 < m1 * 2 ^ (e1 - Min.min e1 e2).toNat :=
          Nat.mul_pos (Nat.pos_of_ne_zero h1) (by positivity)
        have p2 : 0 < m2 * 2 ^ (e2 - Min.min e1 e2).toNat :=
          Nat.mul_pos (Nat.pos_of_ne_zero h2) (by positivity)
        generalize m1 * 2 ^ (e1 - Min.min e1 e2).toNat = A at hS p1
        generalize m2 * 2 ^ (e2 - Min.min e1 e2).toNat = B at hS p2
        cases s1 <;> simp only [signed, Bool.false_eq_true, if_false, if_true] at hS <;> omega
      cases rm <;> cases s1 <;> cases s2 <;>
        simp_all [roundSum, Model.zeroForExactSum, ofM_zero, Model.IEEERoundingMode.asl]
    · rw [if_neg hS0]
      simp only [roundSum, if_neg hS0]
      rw [round_eq h]
      simp [hS0]


private theorem neg_eq_pack (x : Bits f) :
    neg f x = pack f (!signOf f x) (expOf f x) (fracOf f x) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat _ _ _ (expOf_lt x) (fracOf_lt x)]
  conv_lhs => rw [bits_eq_pack x]
  simp only [neg, BitVec.toNat_xor, BitVec.toNat_ofNat]
  rw [pack_toNat _ _ _ (expOf_lt x) (fracOf_lt x)]
  have hb := expOf_lt x
  have hfr := fracOf_lt x
  generalize signOf f x = s
  generalize expOf f x = b at *
  generalize fracOf f x = fr at *
  have h1 : b * 2 ^ f.F + fr < 2 ^ f.E * 2 ^ f.F := by
    have := Nat.mul_le_mul_right (2 ^ f.F) (show b + 1 ≤ 2 ^ f.E by omega)
    rw [Nat.add_mul] at this; omega
  have hk : (2 : Nat) ^ (f.E + f.F) % 2 ^ (1 + f.E + f.F) = 2 ^ (f.E + f.F) :=
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  rw [hk, ← Nat.pow_add] at *
  rw [Nat.add_assoc, Nat.add_assoc]
  generalize b * 2 ^ f.F + fr = r at *
  generalize hK : 2 ^ (f.E + f.F) = K at *
  have hK0 : 0 < K := by rw [← hK]; positivity
  have key : ∀ t : Nat, t < 2 → (K * t + r) ^^^ K = K * (t ^^^ 1) + r := by
    intro t ht
    rw [← Nat.div_add_mod ((K * t + r) ^^^ K) K]
    subst hK
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.mod_self, Nat.div_self hK0,
      Nat.mul_add_div hK0, Nat.div_eq_of_lt h1, Nat.mul_add_mod,
      Nat.mod_eq_of_lt h1, Nat.xor_zero, Nat.add_zero]
  cases s
  · simpa using key 0 (by omega)
  · simpa using key 1 (by omega)


private theorem addDyadic_neg_of_zero (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int)
    (hz : (Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩).significand = 0) :
    (Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩).negative = (s1 && s2) := by
  revert hz
  simp only [Model.addDyadic, FloatLib.Numerics.Dyadic.add, FloatLib.Numerics.Dyadic.addFields]
  split_ifs <;> simp_all

/-- `add_core` for nearest-even, where FloatLib rounds the exact sum directly. -/
private theorem add_core_ne (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    (if m1 = 0 ∧ m2 = 0 ∧ s1 = s2 then zero f s1
      else roundSum f RMode.rne (addExact s1 m1 e1 s2 m2 e2).1 (addExact s1 m1 e1 s2 m2 e2).2) =
    ofM f h (Model.roundDyadic (fl f h) (Model.addDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩)) := by
  have := add_core h .nearestEven s1 m1 e1 s2 m2 e2
  simp only [Model.IEEERoundingMode.asl] at this
  rw [this]
  split_ifs with hz
  · rw [ofM_zeroForExactSum]
    have := ofM_round_zero h .nearestEven _ hz
    simp only [Model.roundDyadicWithRounding] at this
    rw [this, addDyadic_neg_of_zero _ _ _ _ _ _ hz]; simp
  · rfl

/-! ## Unpacking -/

private theorem unpack_eq (x : Bits f) :
    unpack f x = (typeOf f x, signOf f x, (unpack f x).2.2.1, (unpack f x).2.2.2) := by
  unfold typeOf unpack; dsimp only; split_ifs <;> rfl

private theorem unpack_sign (x : Bits f) : (unpack f x).2.1 = signOf f x := by
  rw [unpack_eq x]

private theorem unpack_neg (x : Bits f) :
    unpack f (neg f x) = (typeOf f x, !signOf f x, (unpack f x).2.2.1, (unpack f x).2.2.2) := by
  have hF := fields_pack (!signOf f x) _ _ (expOf_lt x) (fracOf_lt x)
  rw [neg_eq_pack]
  unfold typeOf unpack; dsimp only
  rw [hF.1, hF.2.1, hF.2.2]
  split_ifs <;> rfl

private theorem typeOf_neg (x : Bits f) : typeOf f (neg f x) = typeOf f x := by
  simp [typeOf.eq_def (x := neg f x), unpack_neg]

private theorem mant_eq_zero_iff (x : Bits f) (hn : (typeOf f x).isNaN = false)
    (hi : typeOf f x ≠ .infinity) : typeOf f x = .zero ↔ (unpack f x).2.2.1 = 0 := by
  unfold typeOf unpack at *; dsimp only at *
  split_ifs at * <;> simp_all [FPType.isNaN]

/-! ## Model facts for an encoding -/

private theorem toM_facts (x : Bits f) (hn : (typeOf f x).isNaN = false) :
    Model.isNaN (toM f h x) = false ∧ Model.isSNaN (toM f h x) = false ∧
    Model.isInf (toM f h x) = decide (typeOf f x = .infinity) ∧
    Model.isZero (toM f h x) = decide (typeOf f x = .zero) ∧
    Model.signBit (toM f h x) = signOf f x ∧
    Model.toDyadic? (toM f h x) = if typeOf f x = .infinity then none
      else some ⟨signOf f x, (unpack f x).2.2.1, (unpack f x).2.2.2⟩ := by
  refine ⟨by rw [isNaN_toM, hn], ?_, isInf_toM h x, isZero_toM h x, signBit_toM h x, ?_⟩
  · rw [isSNaN_toM]; revert hn; cases typeOf f x <;> simp [FPType.isNaN]
  · rw [toDyadic?_toM, hn, unpack_sign]; simp

private theorem processNaNs_none {t1 t2 : FPType} {a b : Bits f} (hP : processNaNs f t1 t2 a b = none) :
    t1.isNaN = false ∧ t2.isNaN = false := by
  unfold processNaNs at hP
  split_ifs at hP with h1 h2 h3 h4
  cases t1 <;> cases t2 <;> simp_all [FPType.isNaN]

private theorem processNaNs_some {t1 t2 : FPType} {a b : Bits f} {r : Bits f}
    (hP : processNaNs f t1 t2 a b = some r) : t1.isNaN = true ∨ t2.isNaN = true := by
  unfold processNaNs at hP
  split_ifs at hP <;> simp_all [FPType.isNaN]

/-! ## NaN results -/

private theorem addWithRounding_nan {fmt : FloatFormat} (rm : Mode) (x y n : Model fmt)
    (hn : Model.chooseNaN2 x y = some n)
    (hd : Model.toDyadic? x = none ∨ Model.toDyadic? y = none) :
    Model.addWithRounding rm x y = n := by
  cases rm
  · show Model.add x y = n
    rw [Model.Proof.add_eq_spec]
    rcases hd with hd | hd <;> simp [Model.Spec.add, hd, hn]
  all_goals simp [Model.addWithRounding, Model.withNaNSelection, hn]

private theorem nan_case2 (a b : Bits f) (r : Bits f)
    (hP : processNaNs f (typeOf f a) (typeOf f b) a b = some r) :
    ∃ n, Model.chooseNaN2 (toM f h a) (toM f h b) = some n ∧ ofM f h n = r ∧
      (Model.toDyadic? (toM f h a) = none ∨ Model.toDyadic? (toM f h b) = none) := by
  have := chooseNaN2_toM h a b
  rw [hP] at this
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 this
  refine ⟨n, hn, rfl, ?_⟩
  rcases processNaNs_some hP with h1 | h1
  · left; rw [toDyadic?_toM, h1]; simp
  · right; rw [toDyadic?_toM, h1]; simp

/-! ## Addition -/

theorem add_eq (rm : Mode) (a b : Bits f) :
    IEEE.add f rm.asl a b = ofM f h (Model.addWithRounding rm (toM f h a) (toM f h b)) := by
  unfold IEEE.add
  rw [unpack_eq a, unpack_eq b]
  dsimp only
  cases hP : processNaNs f (typeOf f a) (typeOf f b) a b with
  | some r =>
    obtain ⟨n, hn, rfl, hd⟩ := nan_case2 h a b r hP
    rw [addWithRounding_nan rm _ _ n hn hd]
  | none =>
    dsimp only
    obtain ⟨na, nb⟩ := processNaNs_none hP
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := toM_facts h a na
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := toM_facts h b nb
    have ia := typeOf_inf a
    have ib := typeOf_inf b
    have za := mant_eq_zero_iff a na
    have zb := mant_eq_zero_iff b nb
    generalize hx : toM f h a = x at *
    generalize hy : toM f h b = y at *
    generalize typeOf f a = ta at *
    generalize typeOf f b = tb at *
    generalize signOf f a = sa at *
    generalize signOf f b = sb at *
    generalize (unpack f a).2.2.1 = ma at *
    generalize (unpack f b).2.2.1 = mb at *
    generalize (unpack f a).2.2.2 = ea at *
    generalize (unpack f b).2.2.2 = eb at *
    have ox : ofM f h x = a := by rw [← hx]; rfl
    have oy : ofM f h y = b := by rw [← hy]; rfl
    by_cases hia : ta = .infinity <;> by_cases hib : tb = .infinity
    · have := ia hia; have := ib hib
      cases rm <;> cases sa <;> cases sb <;>
        simp_all [Model.addWithRounding, Model.Proof.add_eq_spec, Model.Spec.add, Model.chooseNaN2,
          Model.withNaNSelection, ofM_invalidResult]
    · have := ia hia
      cases rm <;> cases sa <;>
        simp_all [Model.addWithRounding, Model.Proof.add_eq_spec, Model.Spec.add, Model.chooseNaN2,
          Model.withNaNSelection]
    · have := ib hib
      cases rm <;> cases sb <;>
        simp_all [Model.addWithRounding, Model.Proof.add_eq_spec, Model.Spec.add, Model.chooseNaN2,
          Model.withNaNSelection]
    · simp only [hia, hib, za hia, zb hib, false_and, and_false, or_self, if_false]
      have hc : Model.chooseNaN2 x y = none := by simp [Model.chooseNaN2, a1, a2, b1, b2]
      cases rm
      · show _ = ofM f h (Model.add x y)
        rw [Model.Proof.add_eq_spec]
        simp only [Model.Spec.add, a6, b6, hia, hib, if_false]
        exact add_core_ne h sa ma ea sb mb eb
      all_goals
        simp only [Model.addWithRounding, Model.withNaNSelection, hc, a3, b3, hia, hib,
          decide_false, Bool.false_eq_true, dif_pos, dif_neg, not_false_eq_true]
        have a6' : Model.toDyadic? x = some ⟨sa, ma, ea⟩ := by rw [a6, if_neg hia]
        have b6' : Model.toDyadic? y = some ⟨sb, mb, eb⟩ := by rw [b6, if_neg hib]
        simp only [Model.finiteDyadic_eq_of_toDyadic _ a6', Model.finiteDyadic_eq_of_toDyadic _ b6',
          beq_iff_eq]
        exact add_core h _ sa ma ea sb mb eb

/-! ## Subtraction -/

private theorem toM_neg (b : Bits f) : toM f h (neg f b) = Model.neg (toM f h b) := by
  rw [← ofM_neg h b]; rfl

private theorem sub_eq_add_neg (rm : RMode) (a b : Bits f)
    (hP : processNaNs f (typeOf f a) (typeOf f b) a b = none) :
    IEEE.sub f rm a b = IEEE.add f rm a (neg f b) := by
  obtain ⟨na, nb⟩ := processNaNs_none hP
  have hP' : processNaNs f (typeOf f a) (typeOf f b) a (neg f b) = none := by
    revert na nb; unfold processNaNs
    cases typeOf f a <;> cases typeOf f b <;> simp [FPType.isNaN]
  unfold IEEE.sub IEEE.add
  rw [unpack_eq a, unpack_eq b, unpack_neg b]
  dsimp only
  rw [hP, hP']
  simp only [Bool.not_not]

theorem sub_eq (rm : Mode) (a b : Bits f) :
    IEEE.sub f rm.asl a b =
      match processNaNs f (typeOf f a) (typeOf f b) a b with
      | some r => r
      | none => ofM f h (Model.subWithRounding rm (toM f h a) (toM f h b)) := by
  cases hP : processNaNs f (typeOf f a) (typeOf f b) a b with
  | some r =>
    unfold IEEE.sub
    rw [unpack_eq a, unpack_eq b]
    dsimp only
    rw [hP]
  | none =>
    dsimp only
    rw [sub_eq_add_neg _ _ _ hP, add_eq h, toM_neg]
    rfl

private theorem processNaNs_of_not_nan (a b : Bits f) (ha : (typeOf f a).isNaN = false)
    (hb : (typeOf f b).isNaN = false) : processNaNs f (typeOf f a) (typeOf f b) a b = none := by
  revert ha hb; unfold processNaNs
  cases typeOf f a <;> cases typeOf f b <;> simp [FPType.isNaN]

theorem sub_eq_of_not_nan (rm : Mode) (a b : Bits f) (ha : (typeOf f a).isNaN = false)
    (hb : (typeOf f b).isNaN = false) :
    IEEE.sub f rm.asl a b = ofM f h (Model.subWithRounding rm (toM f h a) (toM f h b)) := by
  rw [sub_eq h, processNaNs_of_not_nan a b ha hb]

/-! ## Multiplication -/

private theorem mulWithRounding_nan {fmt : FloatFormat} (rm : Mode) (x y n : Model fmt)
    (hn : Model.chooseNaN2 x y = some n)
    (hd : Model.toDyadic? x = none ∨ Model.toDyadic? y = none) :
    Model.mulWithRounding rm x y = n := by
  cases rm
  · show Model.mul x y = n
    rw [Model.Proof.mul_eq_spec]
    rcases hd with hd | hd <;> simp [Model.Spec.mul, hd, hn]
  all_goals simp [Model.mulWithRounding, Model.withNaNSelection, hn]

theorem mul_eq (rm : Mode) (a b : Bits f) :
    IEEE.mul f rm.asl a b = ofM f h (Model.mulWithRounding rm (toM f h a) (toM f h b)) := by
  unfold IEEE.mul
  rw [unpack_eq a, unpack_eq b]
  dsimp only
  cases hP : processNaNs f (typeOf f a) (typeOf f b) a b with
  | some r =>
    obtain ⟨n, hn, rfl, hd⟩ := nan_case2 h a b r hP
    rw [mulWithRounding_nan rm _ _ n hn hd]
  | none =>
    dsimp only
    obtain ⟨na, nb⟩ := processNaNs_none hP
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := toM_facts h a na
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := toM_facts h b nb
    have za := mant_eq_zero_iff a na
    have zb := mant_eq_zero_iff b nb
    generalize hx : toM f h a = x at *
    generalize hy : toM f h b = y at *
    generalize typeOf f a = ta at *
    generalize typeOf f b = tb at *
    generalize signOf f a = sa at *
    generalize signOf f b = sb at *
    generalize (unpack f a).2.2.1 = ma at *
    generalize (unpack f b).2.2.1 = mb at *
    generalize (unpack f a).2.2.2 = ea at *
    generalize (unpack f b).2.2.2 = eb at *
    have hc : Model.chooseNaN2 x y = none := by simp [Model.chooseNaN2, a1, a2, b1, b2]
    have hxor : (sa != sb) = Bool.xor sa sb := by cases sa <;> cases sb <;> rfl
    by_cases hia : ta = .infinity <;> by_cases hib : tb = .infinity
    · cases rm <;>
        simp_all [Model.mulWithRounding, Model.Proof.mul_eq_spec, Model.Spec.mul,
          Model.withNaNSelection, ofM_nativeOverflow]
    · by_cases hzb : tb = .zero <;> cases rm <;>
        simp_all [Model.mulWithRounding, Model.Proof.mul_eq_spec, Model.Spec.mul,
          Model.withNaNSelection, ofM_nativeOverflow, ofM_invalidResult]
    · by_cases hza : ta = .zero <;> cases rm <;>
        simp_all [Model.mulWithRounding, Model.Proof.mul_eq_spec, Model.Spec.mul,
          Model.withNaNSelection, ofM_nativeOverflow, ofM_invalidResult]
    · simp only [hia, hib, za hia, zb hib, false_and, and_false, or_self, if_false,]
      have a6' : Model.toDyadic? x = some ⟨sa, ma, ea⟩ := by rw [a6, if_neg hia]
      have b6' : Model.toDyadic? y = some ⟨sb, mb, eb⟩ := by rw [b6, if_neg hib]
      by_cases hz : ma = 0 ∨ mb = 0
      · rw [if_pos hz]
        have hz' : ma * mb = 0 := by rcases hz with hz | hz <;> simp [hz]
        cases rm
        · show _ = ofM f h (Model.mul x y)
          rw [Model.Proof.mul_eq_spec]
          simp [Model.Spec.mul, a6', b6', hz, ofM_zero, hxor]
        all_goals
          simp only [Model.mulWithRounding, Model.withNaNSelection, hc, a3, b3, hia, hib,
            decide_false, Bool.false_eq_true, not_false_eq_true, dif_pos,
            dif_neg, Model.finiteDyadic_eq_of_toDyadic _ a6', Model.finiteDyadic_eq_of_toDyadic _ b6']
          rw [ofM_round_zero h _ _ hz']
      · rw [if_neg hz, round_eq h]
        have hz2 : ¬ (ma = 0 ∨ mb = 0) := hz
        cases rm
        · show _ = ofM f h (Model.mul x y)
          rw [Model.Proof.mul_eq_spec]
          simp only [Model.Spec.mul, a6', b6']
          rw [if_neg (by simpa using hz2), hxor]
          rfl
        all_goals
          simp only [Model.mulWithRounding, Model.withNaNSelection, hc, a3, b3, hia, hib,
            decide_false, Bool.false_eq_true, not_false_eq_true, dif_pos,
            dif_neg, Model.finiteDyadic_eq_of_toDyadic _ a6', Model.finiteDyadic_eq_of_toDyadic _ b6']

/-! ## Fused multiply-add -/

private theorem addExact_comm (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    addExact s1 m1 e1 s2 m2 e2 = addExact s2 m2 e2 s1 m1 e1 := by
  simp only [addExact, min_comm e1 e2, Int.add_comm]

private theorem sum_swap (rm : RMode) (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    (if m1 = 0 ∧ m2 = 0 ∧ s1 = s2 then zero f s1
      else roundSum f rm (addExact s1 m1 e1 s2 m2 e2).1 (addExact s1 m1 e1 s2 m2 e2).2) =
    (if m2 = 0 ∧ m1 = 0 ∧ s2 = s1 then zero f s2
      else roundSum f rm (addExact s2 m2 e2 s1 m1 e1).1 (addExact s2 m2 e2 s1 m1 e1).2) := by
  rw [addExact_comm s1]
  by_cases hc : m1 = 0 ∧ m2 = 0 ∧ s1 = s2
  · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2.symm⟩, hc.2.2]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

private theorem fmaWithRounding_nan {fmt : FloatFormat} (rm : Mode) (x y z n : Model fmt)
    (hn : Model.chooseNaN3 x y z = some n) :
    Model.fmaWithRounding rm x y z = n := by
  cases rm
  · show Model.fma x y z = n
    rw [Model.Proof.fma_eq_spec]
    simp [Model.Spec.fma, hn]
  all_goals simp [Model.fmaWithRounding, Model.withNaNSelection, hn]

private theorem processNaNs3_none {t1 t2 t3 : FPType} {a b c : Bits f}
    (hP : processNaNs3 f t1 t2 t3 a b c = none) :
    t1.isNaN = false ∧ t2.isNaN = false ∧ t3.isNaN = false := by
  unfold processNaNs3 at hP
  split_ifs at hP
  cases t1 <;> cases t2 <;> cases t3 <;> simp_all [FPType.isNaN]

/-- The non-NaN part of `FPMulAdd`. -/
private theorem mulAdd_none (rm : Mode) (c a b : Bits f)
    (hP : processNaNs3 f (typeOf f c) (typeOf f a) (typeOf f b) c a b = none) :
    (let infA := typeOf f c = .infinity; let zeroA := typeOf f c = .zero
     let sA := signOf f c; let s1 := signOf f a; let s2 := signOf f b
     let inf1 := typeOf f a = .infinity; let zero1 := typeOf f a = .zero
     let inf2 := typeOf f b = .infinity; let zero2 := typeOf f b = .zero
     let signP := s1 != s2
     let infP := inf1 ∨ inf2
     let zeroP := zero1 ∨ zero2
     if (inf1 ∧ zero2) ∨ (zero1 ∧ inf2) ∨ (infA ∧ infP ∧ sA ≠ signP) then defaultNaN f
     else if (infA ∧ !sA) ∨ (infP ∧ !signP) then infinity f false
     else if (infA ∧ sA) ∨ (infP ∧ signP) then infinity f true
     else if zeroA ∧ zeroP ∧ sA = signP then zero f sA
     else
       let (m, e) := addExact sA (unpack f c).2.2.1 (unpack f c).2.2.2 signP
         ((unpack f a).2.2.1 * (unpack f b).2.2.1) ((unpack f a).2.2.2 + (unpack f b).2.2.2)
       roundSum f rm.asl m e) =
    ofM f h (Model.fmaWithRounding rm (toM f h a) (toM f h b) (toM f h c)) := by
  obtain ⟨nc, na, nb⟩ := processNaNs3_none hP
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := toM_facts h a na
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := toM_facts h b nb
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := toM_facts h c nc
  have ic := typeOf_inf c
  have za := mant_eq_zero_iff a na
  have zb := mant_eq_zero_iff b nb
  have zc := mant_eq_zero_iff c nc
  generalize hx : toM f h a = x at *
  generalize hy : toM f h b = y at *
  generalize hz : toM f h c = z at *
  have oz : ofM f h z = c := by rw [← hz]; rfl
  generalize typeOf f a = ta at *
  generalize typeOf f b = tb at *
  generalize typeOf f c = tc at *
  generalize signOf f a = sa at *
  generalize signOf f b = sb at *
  generalize signOf f c = sc at *
  generalize (unpack f a).2.2.1 = ma at *
  generalize (unpack f b).2.2.1 = mb at *
  generalize (unpack f c).2.2.1 = mc at *
  generalize (unpack f a).2.2.2 = ea at *
  generalize (unpack f b).2.2.2 = eb at *
  generalize (unpack f c).2.2.2 = ec at *
  have hc3 : Model.chooseNaN3 x y z = none := by
    simp [Model.chooseNaN3, a1, a2, b1, b2, c1, c2]
  have hxor : (sa != sb) = Bool.xor sa sb := by cases sa <;> cases sb <;> rfl
  dsimp only
  by_cases hia : ta = .infinity
  · by_cases hzb : tb = .zero <;> by_cases hic : tc = .infinity <;> cases sa <;> cases sb <;>
      cases sc <;> cases rm <;>
      simp_all [Model.fmaWithRounding, Model.Proof.fma_eq_spec, Model.Spec.fma,
        Model.withNaNSelection, ofM_nativeOverflow, ofM_invalidResult]
  by_cases hib : tb = .infinity
  · by_cases hza : ta = .zero <;> by_cases hic : tc = .infinity <;> cases sa <;> cases sb <;>
      cases sc <;> cases rm <;>
      simp_all [Model.fmaWithRounding, Model.Proof.fma_eq_spec, Model.Spec.fma,
        Model.withNaNSelection, ofM_nativeOverflow, ofM_invalidResult]
  by_cases hic : tc = .infinity
  · have := ic hic
    cases sc <;> cases rm <;>
      simp_all [Model.fmaWithRounding, Model.Proof.fma_eq_spec, Model.Spec.fma,
        Model.withNaNSelection]
  simp only [hia, hib, hic, za hia, zb hib, zc hic, false_and, and_false, or_self, if_false,
    ← Nat.mul_eq_zero]
  rw [sum_swap, hxor]
  have a6' : Model.toDyadic? x = some ⟨sa, ma, ea⟩ := by rw [a6, if_neg hia]
  have b6' : Model.toDyadic? y = some ⟨sb, mb, eb⟩ := by rw [b6, if_neg hib]
  have c6' : Model.toDyadic? z = some ⟨sc, mc, ec⟩ := by rw [c6, if_neg hic]
  cases rm
  · show _ = ofM f h (Model.fma x y z)
    rw [Model.Proof.fma_eq_spec]
    simp only [Model.Spec.fma, hc3, a3, b3, c3, hia, hib, hic, decide_false, Bool.or_false,
      Bool.false_eq_true, if_false, a6', b6', c6']
    exact add_core_ne h _ _ _ sc mc ec
  all_goals
    simp only [Model.fmaWithRounding, Model.withNaNSelection, hc3, a3, b3, c3, hia, hib, hic,
      decide_false, Bool.or_false, Bool.false_eq_true, dif_pos, dif_neg, not_false_eq_true,
      Model.finiteDyadic_eq_of_toDyadic _ a6', Model.finiteDyadic_eq_of_toDyadic _ b6',
      Model.finiteDyadic_eq_of_toDyadic _ c6', beq_iff_eq]
    exact add_core h _ _ _ _ sc mc ec

theorem mulAdd_eq (rm : Mode) (c a b : Bits f) :
    IEEE.mulAdd f rm.asl c a b =
      if typeOf f c = .qnan ∧ ((typeOf f a = .infinity ∧ typeOf f b = .zero) ∨
          (typeOf f a = .zero ∧ typeOf f b = .infinity)) then defaultNaN f
      else match processNaNs3 f (typeOf f c) (typeOf f a) (typeOf f b) c a b with
        | some r => r
        | none => ofM f h (Model.fmaWithRounding rm (toM f h a) (toM f h b) (toM f h c)) := by
  unfold IEEE.mulAdd
  rw [unpack_eq c, unpack_eq a, unpack_eq b]
  dsimp only
  by_cases hq : typeOf f c = .qnan ∧ ((typeOf f a = .infinity ∧ typeOf f b = .zero) ∨
      (typeOf f a = .zero ∧ typeOf f b = .infinity))
  · rw [if_pos hq, if_pos hq]
  · rw [if_neg hq, if_neg hq]
    cases hP : processNaNs3 f (typeOf f c) (typeOf f a) (typeOf f b) c a b with
    | some r => rfl
    | none => dsimp only; exact mulAdd_none h rm c a b hP

theorem mulAdd_eq_of_not_nan (rm : Mode) (c a b : Bits f) (hc : (typeOf f c).isNaN = false)
    (ha : (typeOf f a).isNaN = false) (hb : (typeOf f b).isNaN = false) :
    IEEE.mulAdd f rm.asl c a b =
      ofM f h (Model.fmaWithRounding rm (toM f h a) (toM f h b) (toM f h c)) := by
  have hq : typeOf f c ≠ .qnan := by intro e; rw [e] at hc; simp [FPType.isNaN] at hc
  have hP : processNaNs3 f (typeOf f c) (typeOf f a) (typeOf f b) c a b = none := by
    revert hc ha hb; unfold processNaNs3
    cases typeOf f c <;> cases typeOf f a <;> cases typeOf f b <;> simp [FPType.isNaN]
  rw [mulAdd_eq h, if_neg (fun e => hq e.1), hP]

/-! ## binary32 / binary64 -/

theorem add_eq_b32 (rm : Mode) (a b : Bits .b32) :
    IEEE.add .b32 rm.asl a b =
      ofM .b32 FmtOk.b32 (Model.addWithRounding rm (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  add_eq FmtOk.b32 rm a b
theorem add_eq_b64 (rm : Mode) (a b : Bits .b64) :
    IEEE.add .b64 rm.asl a b =
      ofM .b64 FmtOk.b64 (Model.addWithRounding rm (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  add_eq FmtOk.b64 rm a b

theorem mul_eq_b32 (rm : Mode) (a b : Bits .b32) :
    IEEE.mul .b32 rm.asl a b =
      ofM .b32 FmtOk.b32 (Model.mulWithRounding rm (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  mul_eq FmtOk.b32 rm a b
theorem mul_eq_b64 (rm : Mode) (a b : Bits .b64) :
    IEEE.mul .b64 rm.asl a b =
      ofM .b64 FmtOk.b64 (Model.mulWithRounding rm (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  mul_eq FmtOk.b64 rm a b

theorem sub_eq_b32 (rm : Mode) (a b : Bits .b32) :
    IEEE.sub .b32 rm.asl a b =
      match processNaNs .b32 (typeOf .b32 a) (typeOf .b32 b) a b with
      | some r => r
      | none => ofM .b32 FmtOk.b32
          (Model.subWithRounding rm (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  by rw [sub_eq FmtOk.b32 rm a b]; cases processNaNs .b32 (typeOf .b32 a) (typeOf .b32 b) a b <;> rfl
theorem sub_eq_b64 (rm : Mode) (a b : Bits .b64) :
    IEEE.sub .b64 rm.asl a b =
      match processNaNs .b64 (typeOf .b64 a) (typeOf .b64 b) a b with
      | some r => r
      | none => ofM .b64 FmtOk.b64
          (Model.subWithRounding rm (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  by rw [sub_eq FmtOk.b64 rm a b]; cases processNaNs .b64 (typeOf .b64 a) (typeOf .b64 b) a b <;> rfl

theorem sub_eq_of_not_nan_b32 (rm : Mode) (a b : Bits .b32) (ha : (typeOf .b32 a).isNaN = false)
    (hb : (typeOf .b32 b).isNaN = false) :
    IEEE.sub .b32 rm.asl a b =
      ofM .b32 FmtOk.b32 (Model.subWithRounding rm (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  sub_eq_of_not_nan FmtOk.b32 rm a b ha hb
theorem sub_eq_of_not_nan_b64 (rm : Mode) (a b : Bits .b64) (ha : (typeOf .b64 a).isNaN = false)
    (hb : (typeOf .b64 b).isNaN = false) :
    IEEE.sub .b64 rm.asl a b =
      ofM .b64 FmtOk.b64 (Model.subWithRounding rm (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  sub_eq_of_not_nan FmtOk.b64 rm a b ha hb

theorem mulAdd_eq_b32 (rm : Mode) (c a b : Bits .b32) :
    IEEE.mulAdd .b32 rm.asl c a b =
      if typeOf .b32 c = .qnan ∧ ((typeOf .b32 a = .infinity ∧ typeOf .b32 b = .zero) ∨
          (typeOf .b32 a = .zero ∧ typeOf .b32 b = .infinity)) then defaultNaN .b32
      else match processNaNs3 .b32 (typeOf .b32 c) (typeOf .b32 a) (typeOf .b32 b) c a b with
        | some r => r
        | none => ofM .b32 FmtOk.b32 (Model.fmaWithRounding rm (toM .b32 FmtOk.b32 a)
            (toM .b32 FmtOk.b32 b) (toM .b32 FmtOk.b32 c)) :=
  by
    rw [mulAdd_eq FmtOk.b32 rm c a b]
    cases processNaNs3 .b32 (typeOf .b32 c) (typeOf .b32 a) (typeOf .b32 b) c a b <;> rfl
theorem mulAdd_eq_b64 (rm : Mode) (c a b : Bits .b64) :
    IEEE.mulAdd .b64 rm.asl c a b =
      if typeOf .b64 c = .qnan ∧ ((typeOf .b64 a = .infinity ∧ typeOf .b64 b = .zero) ∨
          (typeOf .b64 a = .zero ∧ typeOf .b64 b = .infinity)) then defaultNaN .b64
      else match processNaNs3 .b64 (typeOf .b64 c) (typeOf .b64 a) (typeOf .b64 b) c a b with
        | some r => r
        | none => ofM .b64 FmtOk.b64 (Model.fmaWithRounding rm (toM .b64 FmtOk.b64 a)
            (toM .b64 FmtOk.b64 b) (toM .b64 FmtOk.b64 c)) :=
  by
    rw [mulAdd_eq FmtOk.b64 rm c a b]
    cases processNaNs3 .b64 (typeOf .b64 c) (typeOf .b64 a) (typeOf .b64 b) c a b <;> rfl

theorem mulAdd_eq_of_not_nan_b32 (rm : Mode) (c a b : Bits .b32)
    (hc : (typeOf .b32 c).isNaN = false) (ha : (typeOf .b32 a).isNaN = false)
    (hb : (typeOf .b32 b).isNaN = false) :
    IEEE.mulAdd .b32 rm.asl c a b = ofM .b32 FmtOk.b32 (Model.fmaWithRounding rm
      (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b) (toM .b32 FmtOk.b32 c)) :=
  mulAdd_eq_of_not_nan FmtOk.b32 rm c a b hc ha hb
theorem mulAdd_eq_of_not_nan_b64 (rm : Mode) (c a b : Bits .b64)
    (hc : (typeOf .b64 c).isNaN = false) (ha : (typeOf .b64 a).isNaN = false)
    (hb : (typeOf .b64 b).isNaN = false) :
    IEEE.mulAdd .b64 rm.asl c a b = ofM .b64 FmtOk.b64 (Model.fmaWithRounding rm
      (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b) (toM .b64 FmtOk.b64 c)) :=
  mulAdd_eq_of_not_nan FmtOk.b64 rm c a b hc ha hb

end IEEE.Spec


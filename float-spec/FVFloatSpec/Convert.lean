import FVFloatSpec.Basic

/-!
# Conversions: `FV/Float/Convert.lean` against FloatLib

`FPRoundInt` is FloatLib's `roundToIntegral` (formats with `F ≤ bias`); `FPConvert` between
formats of different exponent widths is FloatLib's `castWithRounding` off NaNs, and both produce
NaNs on NaNs (payloads differ by design); `FixedToFP` is `roundDyadicWithRounding` of the integer;
`FPToFixed` is FloatLib's `roundDyadicToInt` followed by the Arm `SatQ`; the exact truncation
`truncInt?` is `roundDyadicToInt .towardZero`. The ties-away mode `.rna` is out of scope (FloatLib
has no ties-away operation).
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

/-! ## Integer rounding -/

/-- The Arm integer rounding step (`RoundDown` plus the mode's increment) is FloatLib's
`roundDyadicToInt` on the dyadic `(-1)^s * m * 2^e`. -/
theorem roundToInt_eq (rm : Mode) (s : Bool) (m : Nat) (e : Int) :
    roundToInt rm.asl (signed s m) e = Model.roundDyadicToInt rm ⟨s, m, e⟩ := by
  by_cases hm : m = 0
  · subst hm
    cases rm <;> cases s <;> simp [roundToInt, signed, Model.roundDyadicToInt,
      Model.IEEERoundingMode.asl]
  have hm0 : (m == 0) = false := by simpa using hm
  cases e with
  | ofNat k =>
    cases rm <;> cases s <;>
      simp [roundToInt, signed, Model.roundDyadicToInt, hm, Nat.shiftLeft_eq]
  | negSucc k =>
    have hk : (-Int.negSucc k).toNat = k + 1 := by omega
    have hneg : ¬ (0 ≤ Int.negSucc k) := by omega
    have hD : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hH : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdm := Nat.div_add_mod m (2 ^ (k + 1))
    have hlt := Nat.mod_lt m (Nat.two_pow_pos (k + 1))
    simp only [roundToInt, signed, Model.roundDyadicToInt, hm0, hk, hneg, ite_false,
      FloatLib.Numerics.roundShiftRightEven_def, FloatLib.Numerics.shiftRightRemainder_eq_mod,
      Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
      Nat.add_sub_cancel, Bool.false_eq_true]
    generalize m / 2 ^ (k + 1) = q at *
    generalize m % 2 ^ (k + 1) = r at *
    rw [hD] at hdm hlt ⊢
    generalize 2 ^ k = H at *
    have hr' : m - q * (2 * H) = r := by
      rw [← hdm, Nat.mul_comm q]; omega
    rw [hr']
    cases s
    · have hdiv : (m : Int) / ((2 * H : Nat) : Int) = q ∧ (m : Int) % ((2 * H : Nat) : Int) = r := by
        rw [Int.ediv_emod_unique (by omega)]
        refine ⟨?_, by omega, by omega⟩; rw [← hdm]; push_cast; ring
      simp only [Bool.false_eq_true, ite_false, hdiv.1, hdiv.2]
      cases rm <;> simp [Model.IEEERoundingMode.asl]
      all_goals (split_ifs <;> omega)
    · by_cases hr0 : r = 0
      · have hdiv : (-(m : Int)) / ((2 * H : Nat) : Int) = -(q : Int) ∧
            (-(m : Int)) % ((2 * H : Nat) : Int) = 0 := by
          rw [Int.ediv_emod_unique (by omega)]
          refine ⟨?_, by omega, by omega⟩; rw [← hdm, hr0]; push_cast; ring
        simp only [ite_true, hdiv.1, hdiv.2]
        cases rm <;> simp [Model.IEEERoundingMode.asl, hr0]
        all_goals (split_ifs <;> omega)
      · have hdiv : (-(m : Int)) / ((2 * H : Nat) : Int) = -(q : Int) - 1 ∧
            (-(m : Int)) % ((2 * H : Nat) : Int) = 2 * H - r := by
          rw [Int.ediv_emod_unique (by omega)]
          refine ⟨?_, by omega, by omega⟩; rw [← hdm]; push_cast; ring
        simp only [ite_true, hdiv.1, hdiv.2]
        cases rm <;> simp [Model.IEEERoundingMode.asl, hr0] <;> (try split_ifs) <;> omega

namespace Convert

/-! ## Fields of encodings -/

private theorem pow_EF (f : Fmt) : 2 ^ (f.E + f.F) = 2 ^ f.E * 2 ^ f.F :=
  Nat.pow_add 2 f.E f.F

private theorem pack_toNat (f : Fmt) (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E)
    (hfr : fr < 2 ^ f.F) :
    (pack f s b fr).toNat = fr + 2 ^ f.F * ((if s then 2 ^ f.E else 0) + b) := by
  have h1 : (b + 1) * 2 ^ f.F ≤ 2 ^ f.E * 2 ^ f.F := Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ (1 + f.E + f.F) = 2 * (2 ^ f.E * 2 ^ f.F) := by
    rw [Nat.add_assoc, Nat.pow_add, pow_EF]
  unfold pack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, pow_EF]
  · cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> ring
  · rw [h2, pow_EF, Nat.add_mul] at *
    cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> omega

private theorem fields_pack (f : Fmt) (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E)
    (hfr : fr < 2 ^ f.F) :
    signOf f (pack f s b fr) = s ∧ expOf f (pack f s b fr) = b ∧
      fracOf f (pack f s b fr) = fr := by
  have hP := Nat.two_pow_pos f.F
  simp only [signOf, expOf, fracOf, pack_toNat f s b fr hb hfr]
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_EF, Nat.mul_comm (2 ^ f.E)]
    have h1 : 2 ^ f.F * (b + 1) ≤ 2 ^ f.F * 2 ^ f.E := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add] at h1
    cases s <;> simp only [ite_true, ite_false, Bool.false_eq_true, Nat.mul_add,
      Nat.zero_add, decide_eq_true_eq, decide_eq_false_iff_not] <;>
      generalize 2 ^ f.F * 2 ^ f.E = QP at * <;> generalize 2 ^ f.F * b = B at * <;> omega
  · rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hfr, Nat.zero_add]
    cases s <;> simp [Nat.mod_eq_of_lt hb]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfr]

private theorem pack_fields (f : Fmt) (x : Bits f) :
    pack f (signOf f x) (expOf f x) (fracOf f x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hP := Nat.two_pow_pos f.F
  have hQ := Nat.two_pow_pos f.E
  have hb : expOf f x < 2 ^ f.E := Nat.mod_lt _ hQ
  have hfr : fracOf f x < 2 ^ f.F := Nat.mod_lt _ hP
  rw [pack_toNat f _ _ _ hb hfr]
  have hx : x.toNat < 2 * (2 ^ f.E * 2 ^ f.F) := by
    have h0 : x.toNat < 2 ^ (1 + f.E + f.F) := x.isLt
    have h2 : (2 : Nat) ^ (1 + f.E + f.F) = 2 * (2 ^ f.E * 2 ^ f.F) := by
      rw [Nat.add_assoc, Nat.pow_add, pow_EF]
    omega
  have hmod := Nat.mod_mul (a := 2 ^ f.F) (b := 2 ^ f.E) (x := x.toNat)
  rw [Nat.mul_comm (2 ^ f.F) (2 ^ f.E)] at hmod
  have hdm := Nat.div_add_mod x.toNat (2 ^ f.E * 2 ^ f.F)
  simp only [signOf, expOf, fracOf, pow_EF]
  have hQP : 0 < 2 ^ f.E * 2 ^ f.F := Nat.mul_pos hQ hP
  by_cases hs : 2 ^ f.E * 2 ^ f.F ≤ x.toNat
  · have h1 : x.toNat / (2 ^ f.E * 2 ^ f.F) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp only [hs, decide_true, ite_true]
    rw [Nat.mul_add, Nat.mul_comm (2 ^ f.F) (2 ^ f.E)]
    rw [h1] at hdm
    omega
  · have h1 : x.toNat / (2 ^ f.E * 2 ^ f.F) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [hs, decide_false, ite_false, Bool.false_eq_true, Nat.zero_add]
    rw [h1] at hdm
    omega

/-! ## Rounding an exactly representable integer -/

private theorem bias_pos {f : Fmt} (h : FmtOk f) : 1 ≤ f.bias := by
  have := h.E2
  have : 2 ≤ 2 ^ (f.E - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.E - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold Fmt.bias; omega

private theorem expOnes_eq {f : Fmt} (h : FmtOk f) : f.expOnes = 2 * f.bias + 1 := by
  have := h.E2
  have h2 : 2 ^ f.E = 2 * 2 ^ (f.E - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (f.E - 1) := Nat.one_le_two_pow
  unfold Fmt.expOnes Fmt.bias; omega

/-- `FPRound` of a positive integer `a * 2^k` with at most `F + 1` significant bits and below
`2^(bias+1)` is exact, so it does not depend on the rounding mode. -/
private theorem round_exact_int {f : Fmt} (h : FmtOk f) (rm : RMode) (s : Bool) (a k : Nat)
    (ha0 : 0 < a) (ha : a < 2 ^ (f.F + 1)) (hov : a * 2 ^ k < 2 ^ (f.bias + 1)) :
    round f rm s (a * 2 ^ k) 0 = round f .rz s (a * 2 ^ k) 0 := by
  have hb1 := bias_pos h
  have hones := expOnes_eq h
  have hn0 : a * 2 ^ k ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
  have hL1 : (a * 2 ^ k).log2 < f.F + 1 + k := by
    rw [Nat.log2_lt hn0, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos k)
  have hL2 : (a * 2 ^ k).log2 ≤ f.bias := by
    have := (Nat.log2_lt hn0).2 hov; omega
  have hdvd : 2 ^ ((a * 2 ^ k).log2 - f.F) ∣ a * 2 ^ k :=
    Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) a
  generalize hn : a * 2 ^ k = n at *
  generalize hL : n.log2 = L at *
  have hmax : Max.max ((L : Int) - (1 - (f.bias : Int)) + 1) 0 = L + f.bias := by omega
  have hne : ¬ ((L : Int) + f.bias = 0) := by omega
  have hpair : (if (L : Int) - f.F ≤ 0 then
        (n * 2 ^ (-((L : Int) - f.F)).toNat, if false = true then Err.low else Err.exact)
      else truncShift n ((L : Int) - f.F).toNat false) =
      (if (L : Int) - f.F ≤ 0 then n * 2 ^ (-((L : Int) - f.F)).toNat
        else n / 2 ^ ((L : Int) - f.F).toNat, Err.exact) := by
    by_cases h1 : (L : Int) - f.F ≤ 0
    · simp only [h1, ite_true, Bool.false_eq_true, ite_false]
    · have h2 : ((L : Int) - f.F).toNat = L - f.F := by omega
      simp only [h1, ite_false, h2]
      simp [truncShift, Nat.mod_eq_zero_of_dvd hdvd]
  have hov' : ¬ ((f.expOnes : Int) ≤ L + f.bias) := by omega
  simp only [round, hn0, ite_false, Fmt.minExp, hL, Int.add_zero, Int.sub_zero]
  simp only [hmax, hne, ite_false]
  simp only [hpair]
  cases rm <;> simp [hov']

/-! ## Facts about `unpack` -/

private theorem unpack_sign (f : Fmt) (x : Bits f) : (unpack f x).2.1 = signOf f x := by
  unfold unpack; dsimp only; split_ifs <;> rfl

private theorem unpack_zero (f : Fmt) (x : Bits f)
    (ht : (unpack f x).1 = .zero ∨ (unpack f x).1.isNaN) :
    (unpack f x).2.2.1 = 0 ∧ (unpack f x).2.2.2 = 0 := by
  unfold unpack at *; dsimp only at *; split_ifs at * <;> simp_all [FPType.isNaN]

/-- A finite nonzero operand: a mantissa of at most `F + 1` bits, and a value below
`2^(bias+1)` when the exponent is nonnegative. -/
private theorem unpack_finite {f : Fmt} (h : FmtOk f) (x : Bits f)
    (ht : (unpack f x).1 = .denormal ∨ (unpack f x).1 = .nonzero) :
    0 < (unpack f x).2.2.1 ∧ (unpack f x).2.2.1 < 2 ^ (f.F + 1) ∧
      ∀ k : Nat, (unpack f x).2.2.2 = k → (unpack f x).2.2.1 * 2 ^ k < 2 ^ (f.bias + 1) := by
  have hb1 := bias_pos h
  have hones := expOnes_eq h
  have hF : 2 ^ (f.F + 1) = 2 * 2 ^ f.F := by rw [Nat.pow_succ]; omega
  have hfr : fracOf f x < 2 ^ f.F := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hex : expOf f x < 2 ^ f.E := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hE : 2 ^ f.E = f.expOnes + 1 := by
    unfold Fmt.expOnes; have := Nat.one_le_two_pow (n := f.E); omega
  unfold unpack at ht ⊢
  dsimp only at ht ⊢
  split_ifs at ht ⊢ with h1 h2 h3 h4
  all_goals try (simp at ht; done)
  all_goals dsimp only
  · have := h.F1
    simp only [Fmt.minExp]
    refine ⟨by omega, by omega, fun k hk => by omega⟩
  · refine ⟨by omega, by omega, fun k hk => ?_⟩
    have hlt : (2 ^ f.F + fracOf f x) * 2 ^ k < 2 ^ (f.F + 1) * 2 ^ k :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos k)
    rw [← Nat.pow_add] at hlt
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))

private theorem unpack_inf (f : Fmt) (x : Bits f) (h : FmtOk f)
    (ht : (unpack f x).1 = .infinity) :
    x = infinity f (signOf f x) := by
  have hones := expOnes_eq h
  have hb1 := bias_pos h
  unfold unpack at ht
  dsimp only at ht
  split_ifs at ht with h1 h2 h3
  conv_lhs => rw [← pack_fields f x]
  unfold infinity
  rw [h3, ‹fracOf f x = 0›]

/-- Directed integer rounding of a dyadic with a negative exponent and an `F + 1`-bit
significand has magnitude at most `2^F`. -/
private theorem natAbs_roundDyadicToInt_negSucc (rm : Mode) (s : Bool) (m j F : Nat)
    (hm : m < 2 ^ (F + 1)) :
    (Model.roundDyadicToInt rm ⟨s, m, Int.negSucc j⟩).natAbs ≤ 2 ^ F := by
  have hq : m / 2 ^ (j + 1) < 2 ^ F := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc m < 2 ^ (F + 1) := hm
      _ = 2 ^ F * 2 ^ 1 := Nat.pow_add 2 F 1
      _ ≤ 2 ^ F * 2 ^ (j + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 := FloatLib.Numerics.roundShiftRightEven_le_shiftRight_add1 m (j + 1)
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] at h1
  simp only [Model.roundDyadicToInt]
  by_cases h0 : m = 0
  · simp [h0]
  · rw [ite_eq_right_of_eq_false _ _ (by simpa using h0)]
    have hM : ∀ M : Nat, M ≤ m / 2 ^ (j + 1) + 1 →
        (if s = true then -Int.ofNat M else Int.ofNat M).natAbs ≤ 2 ^ F := by
      intro M hM; cases s <;> simp <;> omega
    apply hM
    cases rm <;> dsimp only <;>
      (try simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] at h1 ⊢) <;>
      (try split_ifs) <;> omega

/-- The finite nonzero case of `FPRoundInt`: the integer is FloatLib's, and encoding it with
`FPRound` toward zero is FloatLib's encoding in the requested mode, since it is exact. -/
private theorem roundInt_finite {f : Fmt} (h : FmtOk f) (hFb : f.F ≤ f.bias) (rm : Mode)
    (s : Bool) (m : Nat) (e : Int) (h0 : 0 < m) (hm : m < 2 ^ (f.F + 1))
    (hk : ∀ k : Nat, e = k → m * 2 ^ k < 2 ^ (f.bias + 1)) :
    (if roundToInt rm.asl (signed s m) e = 0 then zero f s
      else round f .rz (decide (roundToInt rm.asl (signed s m) e < 0))
        (roundToInt rm.asl (signed s m) e).natAbs 0) =
    ofM f h (if Model.roundDyadicToInt rm ⟨s, m, e⟩ = 0 then Model.zero (fl f h) s
      else Model.roundDyadicWithRounding (fl f h) rm
        (FloatLib.Numerics.Dyadic.ofScaledInt (Model.roundDyadicToInt rm ⟨s, m, e⟩) 0)) := by
  rw [roundToInt_eq]
  generalize hc : Model.roundDyadicToInt rm ⟨s, m, e⟩ = c
  by_cases hc0 : c = 0
  · simp [hc0, ofM_zero h]
  simp only [hc0, ite_false]
  rw [show FloatLib.Numerics.Dyadic.ofScaledInt c 0 = ⟨decide (c < 0), c.natAbs, 0⟩ from rfl,
    ← round_eq h]
  cases e with
  | ofNat k =>
    have habs : c.natAbs = m * 2 ^ k := by
      rw [← hc]
      cases s <;> simp [Model.roundDyadicToInt, h0.ne', Nat.shiftLeft_eq, Int.natAbs_mul,
        Int.natAbs_pow]
    rw [habs]
    exact (round_exact_int h _ _ m k h0 hm (hk k rfl)).symm
  | negSucc j =>
    have hle := natAbs_roundDyadicToInt_negSucc rm s m j f.F hm
    rw [hc] at hle
    have hF1 : 2 ^ (f.F + 1) = 2 * 2 ^ f.F := by rw [Nat.pow_succ]; omega
    have hFb' : 2 ^ f.F ≤ 2 ^ f.bias := Nat.pow_le_pow_right (by omega) hFb
    have hb1 : 2 ^ (f.bias + 1) = 2 * 2 ^ f.bias := by rw [Nat.pow_succ]; omega
    have h2 : c.natAbs = c.natAbs * 2 ^ 0 := by simp
    rw [h2]
    exact (round_exact_int h _ _ c.natAbs 0 (by omega) (by omega) (by simp; omega)).symm

/-- Truncation toward zero of `(-1)^s * m * 2^e` is FloatLib's `roundDyadicToInt .towardZero`. -/
private theorem trunc_eq (s : Bool) (m : Nat) (e : Int) :
    signed s (if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat) =
      Model.roundDyadicToInt .towardZero ⟨s, m, e⟩ := by
  by_cases hm : m = 0
  · subst hm; cases s <;> simp [signed, Model.roundDyadicToInt]
  cases e with
  | ofNat k => cases s <;> simp [signed, Model.roundDyadicToInt, hm, Nat.shiftLeft_eq]
  | negSucc j =>
    have hneg : ¬ (0 ≤ Int.negSucc j) := by omega
    cases s <;> simp [signed, Model.roundDyadicToInt, hm, hneg, Nat.shiftRight_eq_div_pow]

private theorem satQ_zero (M : Nat) (u : Bool) : satQ 0 M u = 0 := by
  have h1 : (0 : Int) < 2 ^ (M - 1) := by positivity
  unfold satQ; cases u <;> simp [not_lt.mpr h1.le, not_le.mpr h1]

private theorem round_zero (f : Fmt) (rm : RMode) (s : Bool) (e : Int) :
    round f rm s 0 e = zero f s := by
  simp [round]

private theorem cast_of_finite {A B : FloatFormat} (hE : A.expWidth ≠ B.expWidth)
    (y : Model A) (rm : Mode) (d : FloatLib.Numerics.Dyadic) (hnan : Model.isNaN y = false)
    (hinf : Model.isInf y = false) (hd : Model.toDyadic? y = some d) :
    Model.castWithRounding A B y rm = Model.roundDyadicWithRounding B rm d := by
  have hne : A ≠ B := fun heq => hE (congrArg FloatFormat.expWidth heq)
  cases rm <;>
    simp [Model.castWithRounding, Model.cast, hnan, hinf, hne, hE,
      Model.finiteDyadic_eq_of_toDyadic _ hd, Model.roundDyadicWithRounding]

private theorem cast_of_inf {A B : FloatFormat} (y : Model A) (rm : Mode)
    (hnan : Model.isNaN y = false) (hinf : Model.isInf y = true) :
    Model.castWithRounding A B y rm = Model.nativeOverflow B (Model.signBit y) := by
  cases rm <;> simp [Model.castWithRounding, Model.cast, hnan, hinf]

private theorem cast_of_nan {A B : FloatFormat} (hne : A ≠ B) (y : Model A) (rm : Mode)
    (hnan : Model.isNaN y = true) :
    Model.castWithRounding A B y rm =
      Model.propagatedNaN B (Model.signBit y) (Model.nanPayload y) := by
  cases rm <;> simp [Model.castWithRounding, Model.cast, hnan, hne]

private theorem expOnes_lt (f : Fmt) : f.expOnes < 2 ^ f.E := by
  unfold Fmt.expOnes; have := Nat.one_le_two_pow (n := f.E); omega

/-- An all-ones exponent with the quiet bit set is a quiet NaN. -/
private theorem typeOf_pack_qnan {f : Fmt} (h : FmtOk f) (s : Bool) (fr : Nat)
    (h1 : 2 ^ (f.F - 1) ≤ fr) (h2 : fr < 2 ^ f.F) :
    typeOf f (pack f s f.expOnes fr) = .qnan := by
  obtain ⟨-, he, hf⟩ := fields_pack f s f.expOnes fr (expOnes_lt f) h2
  have hones := expOnes_eq h
  have : 1 ≤ 2 ^ (f.F - 1) := Nat.one_le_two_pow
  unfold typeOf unpack
  simp only [he, hf]
  simp [show f.expOnes ≠ 0 by omega, show fr ≠ 0 by omega, h1]

end Convert

/-! ## `FPRoundInt` -/

theorem roundInt_eq {f : Fmt} (h : FmtOk f) (hFb : f.F ≤ f.bias) (rm : Mode) (x : Bits f) :
    IEEE.roundInt f rm.asl x = ofM f h (Model.roundToIntegral (toM f h x) rm) := by
  have hd := toDyadic?_toM h x
  have hinf := isInf_toM h x
  have hs := Convert.unpack_sign f x
  have hz := Convert.unpack_zero f x
  have hfin := Convert.unpack_finite h x
  have hI := Convert.unpack_inf f x h
  have hq := ofM_quietNaN h x
  unfold IEEE.roundInt Model.roundToIntegral Model.roundToIntegralExactWithStatus Model.exactValue
  rw [hd]
  unfold typeOf at hd hinf hq ⊢
  rcases hu : unpack f x with ⟨t, s, m, e⟩
  rw [hu] at hs hz hfin hI hq
  simp only [hu] at hinf ⊢
  dsimp only at hs hz hfin hI hq
  subst hs
  cases t
  · -- zero
    obtain ⟨rfl, rfl⟩ := hz (Or.inl rfl)
    simp [FPType.isNaN, Model.roundDyadicToInt, ofM_zero h]
  · -- denormal
    obtain ⟨h0, hm, hk⟩ := hfin (Or.inl rfl)
    simp [FPType.isNaN]
    exact Convert.roundInt_finite h hFb rm _ m e h0 hm hk
  · obtain ⟨h0, hm, hk⟩ := hfin (Or.inr rfl)
    simp [FPType.isNaN]
    exact Convert.roundInt_finite h hFb rm _ m e h0 hm hk
  · -- infinity
    simp [FPType.isNaN, hinf, Model.outcomeWithInvalid]
    exact (hI rfl).symm
  · -- qnan
    simp [FPType.isNaN, hinf, Model.outcomeWithInvalid]
    exact (hq rfl).symm
  · simp [FPType.isNaN, hinf, Model.outcomeWithInvalid]
    exact (hq rfl).symm

/-! ## Truncation, `FPToFixed`, `FixedToFP` -/

theorem truncInt?_eq {f : Fmt} (h : FmtOk f) (x : Bits f) :
    IEEE.truncInt? f x = match Model.exactValue (toM f h x) with
      | .finite d => some (Model.roundDyadicToInt .towardZero d)
      | _ => none := by
  have hd := toDyadic?_toM h x
  unfold IEEE.truncInt? Model.exactValue
  rw [hd]
  unfold typeOf
  rcases hu : unpack f x with ⟨t, s, m, e⟩
  cases t <;> simp [FPType.isNaN, Convert.trunc_eq] <;> split <;> (try split_ifs at *) <;>
    simp_all

theorem toFixed_eq {f : Fmt} (h : FmtOk f) (x : Bits f) (u : Bool) (M : Nat) (rm : Mode) :
    IEEE.toFixed f x u M rm.asl = match Model.exactValue (toM f h x) with
      | .finite d => satQ (Model.roundDyadicToInt rm d) M u
      | .infinity s => satQ (signed s (2 ^ M)) M u
      | .nan .. => 0 := by
  have hd := toDyadic?_toM h x
  have hinf := isInf_toM h x
  have hsg := signBit_toM h x
  have hs := Convert.unpack_sign f x
  have hz := Convert.unpack_zero f x
  unfold IEEE.toFixed Model.exactValue
  rw [hd]
  unfold typeOf at hd hinf ⊢
  rcases hu : unpack f x with ⟨t, s, m, e⟩
  rw [hu] at hs hz
  simp only [hu] at hinf ⊢
  dsimp only at hs hz
  subst hs
  cases t
  · simp [FPType.isNaN, roundToInt_eq]
  · simp [FPType.isNaN, roundToInt_eq]
  · simp [FPType.isNaN, roundToInt_eq]
  · simp [FPType.isNaN, hinf, hsg]
  · obtain ⟨rfl, rfl⟩ := hz (Or.inr rfl)
    simp [FPType.isNaN, hinf, roundToInt, signed, Convert.satQ_zero]
  · obtain ⟨rfl, rfl⟩ := hz (Or.inr rfl)
    simp [FPType.isNaN, hinf, roundToInt, signed, Convert.satQ_zero]

theorem fromFixed_eq {f : Fmt} (h : FmtOk f) (M : Nat) (x : BitVec M) (u : Bool) (rm : Mode) :
    IEEE.fromFixed f M x u rm.asl =
      let i : Int := if u then (x.toNat : Int) else x.toInt
      ofM f h (Model.roundDyadicWithRounding (fl f h) rm ⟨decide (i < 0), i.natAbs, 0⟩) := by
  unfold IEEE.fromFixed
  dsimp only
  rw [← round_eq h]
  generalize (if u then (x.toNat : Int) else x.toInt) = i
  by_cases hi : i = 0
  · subst hi; simp [Convert.round_zero]
  · simp [hi]

/-! ## `FPConvert` -/

/-- `FPConvert` between formats with different exponent widths (e.g. binary32 ↔ binary64) is
FloatLib's `castWithRounding` on non-NaN operands; NaNs go through `FPConvertNaN`. -/
theorem convert_eq {src dst : Fmt} (hs : FmtOk src) (hd : FmtOk dst) (hE : src.E ≠ dst.E)
    (rm : Mode) (x : Bits src) :
    IEEE.convert src dst rm.asl x =
      if (typeOf src x).isNaN then convertNaN src dst x
      else ofM dst hd (Model.castWithRounding (fl src hs) (fl dst hd) (toM src hs x) rm) := by
  have hn := isNaN_toM hs x
  have hi := isInf_toM hs x
  have hsg := signBit_toM hs x
  have hdy := toDyadic?_toM hs x
  have hus := Convert.unpack_sign src x
  have hz := Convert.unpack_zero src x
  have hfin := Convert.cast_of_finite (A := fl src hs) (B := fl dst hd) hE (toM src hs x) rm
  have hinf := Convert.cast_of_inf (A := fl src hs) (B := fl dst hd) (toM src hs x) rm
  unfold IEEE.convert
  unfold typeOf at hn hi hdy ⊢
  rcases hu : unpack src x with ⟨t, s, m, e⟩
  rw [hu] at hus hz
  simp only [hu] at hn hi hdy ⊢
  dsimp only at hus hz
  subst hus
  cases t <;> simp only [FPType.isNaN, reduceCtorEq, or_false, false_or, or_self, ite_false,
    ite_true, Bool.false_eq_true, decide_false, decide_true] at hn hi hdy ⊢
  · obtain ⟨rfl, rfl⟩ := hz (Or.inl rfl)
    rw [hfin _ hn hi hdy, ← round_eq hd, Convert.round_zero]
  · rw [hfin _ hn hi hdy, ← round_eq hd]
  · rw [hfin _ hn hi hdy, ← round_eq hd]
  · rw [hinf hn hi, hsg, ofM_nativeOverflow hd]

theorem convert_eq_of_not_nan {src dst : Fmt} (hs : FmtOk src) (hd : FmtOk dst)
    (hE : src.E ≠ dst.E) (rm : Mode) (x : Bits src) (hx : (typeOf src x).isNaN = false) :
    IEEE.convert src dst rm.asl x =
      ofM dst hd (Model.castWithRounding (fl src hs) (fl dst hd) (toM src hs x) rm) := by
  rw [convert_eq hs hd hE, hx]; rfl

/-- On a NaN, both `FPConvertNaN` and FloatLib's cast produce NaNs (their payloads differ by
design: the Arm conversion shifts or truncates the payload, FloatLib keeps it only if it fits). -/
theorem convert_isNaN {src dst : Fmt} (hs : FmtOk src) (hd : FmtOk dst) (hE : src.E ≠ dst.E)
    (rm : Mode) (x : Bits src) (hx : (typeOf src x).isNaN = true) :
    (typeOf dst (convertNaN src dst x)).isNaN = true ∧
      Model.isNaN (Model.castWithRounding (fl src hs) (fl dst hd) (toM src hs x) rm) = true := by
  have hsF := hs.F1
  have hdF := hd.F1
  have hdq : 2 ^ dst.F = 2 * 2 ^ (dst.F - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  constructor
  · unfold convertNaN
    dsimp only
    rw [Convert.typeOf_pack_qnan hd]
    · rfl
    · omega
    · have hp : fracOf src x % 2 ^ (src.F - 1) < 2 ^ (src.F - 1) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      generalize fracOf src x % 2 ^ (src.F - 1) = p at *
      suffices (if src.F ≤ dst.F then p * 2 ^ (dst.F - src.F) else p / 2 ^ (src.F - dst.F)) <
          2 ^ (dst.F - 1) by omega
      split_ifs with hle
      · calc p * 2 ^ (dst.F - src.F) < 2 ^ (src.F - 1) * 2 ^ (dst.F - src.F) :=
              Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
          _ = 2 ^ (dst.F - 1) := by rw [← Nat.pow_add]; congr 1; omega
      · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
        calc p < 2 ^ (src.F - 1) := hp
          _ = 2 ^ (dst.F - 1 + (src.F - dst.F)) := by congr 1; omega
  · have hne : fl src hs ≠ fl dst hd := fun heq => hE (congrArg FloatFormat.expWidth heq)
    have hn : Model.isNaN (toM src hs x) = true := by rw [isNaN_toM hs x, hx]
    rw [Convert.cast_of_nan hne _ rm hn]
    generalize Model.signBit (toM src hs x) = sg
    generalize Model.nanPayload (toM src hs x) = p
    have hfr : 2 ^ (dst.F - 1) + (if p < 2 ^ (dst.F - 1) then p else 0) < 2 ^ dst.F := by
      have hdq : 2 ^ dst.F = 2 * 2 ^ (dst.F - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have : 1 ≤ 2 ^ (dst.F - 1) := Nat.one_le_two_pow
      split_ifs <;> omega
    have hp : Model.propagatedNaN (fl dst hd) sg p = Model.ofFields (fl dst hd) sg dst.expOnes
        (2 ^ (dst.F - 1) + if p < 2 ^ (dst.F - 1) then p else 0) := rfl
    have := isNaN_toM hd (ofM dst hd (Model.propagatedNaN (fl dst hd) sg p))
    rw [toM_ofM] at this
    rw [this, hp, ofM_ofFields hd _ _ _ (Convert.expOnes_lt dst) hfr,
      Convert.typeOf_pack_qnan hd _ _ (by omega) hfr]
    rfl

/-! ## binary32 / binary64 instances -/

theorem roundInt_eq_b32 (rm : Mode) (x : Bits .b32) :
    IEEE.roundInt .b32 rm.asl x =
      ofM .b32 FmtOk.b32 (Model.roundToIntegral (toM .b32 FmtOk.b32 x) rm) :=
  roundInt_eq FmtOk.b32 (by decide) rm x

theorem roundInt_eq_b64 (rm : Mode) (x : Bits .b64) :
    IEEE.roundInt .b64 rm.asl x =
      ofM .b64 FmtOk.b64 (Model.roundToIntegral (toM .b64 FmtOk.b64 x) rm) :=
  roundInt_eq FmtOk.b64 (by decide) rm x

theorem convert_eq_b32_b64 (rm : Mode) (x : Bits .b32) :
    IEEE.convert .b32 .b64 rm.asl x =
      if (typeOf .b32 x).isNaN then convertNaN .b32 .b64 x
      else ofM .b64 FmtOk.b64 (Model.castWithRounding (fl .b32 FmtOk.b32) (fl .b64 FmtOk.b64)
        (toM .b32 FmtOk.b32 x) rm) :=
  convert_eq FmtOk.b32 FmtOk.b64 (by decide) rm x

theorem convert_eq_b64_b32 (rm : Mode) (x : Bits .b64) :
    IEEE.convert .b64 .b32 rm.asl x =
      if (typeOf .b64 x).isNaN then convertNaN .b64 .b32 x
      else ofM .b32 FmtOk.b32 (Model.castWithRounding (fl .b64 FmtOk.b64) (fl .b32 FmtOk.b32)
        (toM .b64 FmtOk.b64 x) rm) :=
  convert_eq FmtOk.b64 FmtOk.b32 (by decide) rm x

theorem convert_eq_of_not_nan_b32_b64 (rm : Mode) (x : Bits .b32)
    (hx : (typeOf .b32 x).isNaN = false) :
    IEEE.convert .b32 .b64 rm.asl x =
      ofM .b64 FmtOk.b64 (Model.castWithRounding (fl .b32 FmtOk.b32) (fl .b64 FmtOk.b64)
        (toM .b32 FmtOk.b32 x) rm) :=
  convert_eq_of_not_nan FmtOk.b32 FmtOk.b64 (by decide) rm x hx

theorem convert_eq_of_not_nan_b64_b32 (rm : Mode) (x : Bits .b64)
    (hx : (typeOf .b64 x).isNaN = false) :
    IEEE.convert .b64 .b32 rm.asl x =
      ofM .b32 FmtOk.b32 (Model.castWithRounding (fl .b64 FmtOk.b64) (fl .b32 FmtOk.b32)
        (toM .b64 FmtOk.b64 x) rm) :=
  convert_eq_of_not_nan FmtOk.b64 FmtOk.b32 (by decide) rm x hx

theorem convert_isNaN_b32_b64 (rm : Mode) (x : Bits .b32) (hx : (typeOf .b32 x).isNaN = true) :
    (typeOf .b64 (convertNaN .b32 .b64 x)).isNaN = true ∧
      Model.isNaN (Model.castWithRounding (fl .b32 FmtOk.b32) (fl .b64 FmtOk.b64)
        (toM .b32 FmtOk.b32 x) rm) = true :=
  convert_isNaN FmtOk.b32 FmtOk.b64 (by decide) rm x hx

theorem convert_isNaN_b64_b32 (rm : Mode) (x : Bits .b64) (hx : (typeOf .b64 x).isNaN = true) :
    (typeOf .b32 (convertNaN .b64 .b32 x)).isNaN = true ∧
      Model.isNaN (Model.castWithRounding (fl .b64 FmtOk.b64) (fl .b32 FmtOk.b32)
        (toM .b64 FmtOk.b64 x) rm) = true :=
  convert_isNaN FmtOk.b64 FmtOk.b32 (by decide) rm x hx

theorem fromFixed_eq_b32 (M : Nat) (x : BitVec M) (u : Bool) (rm : Mode) :
    IEEE.fromFixed .b32 M x u rm.asl =
      let i : Int := if u then (x.toNat : Int) else x.toInt
      ofM .b32 FmtOk.b32
        (Model.roundDyadicWithRounding (fl .b32 FmtOk.b32) rm ⟨decide (i < 0), i.natAbs, 0⟩) :=
  fromFixed_eq FmtOk.b32 M x u rm

theorem fromFixed_eq_b64 (M : Nat) (x : BitVec M) (u : Bool) (rm : Mode) :
    IEEE.fromFixed .b64 M x u rm.asl =
      let i : Int := if u then (x.toNat : Int) else x.toInt
      ofM .b64 FmtOk.b64
        (Model.roundDyadicWithRounding (fl .b64 FmtOk.b64) rm ⟨decide (i < 0), i.natAbs, 0⟩) :=
  fromFixed_eq FmtOk.b64 M x u rm

theorem toFixed_eq_b32 (x : Bits .b32) (u : Bool) (M : Nat) (rm : Mode) :
    IEEE.toFixed .b32 x u M rm.asl = match Model.exactValue (toM .b32 FmtOk.b32 x) with
      | .finite d => satQ (Model.roundDyadicToInt rm d) M u
      | .infinity s => satQ (signed s (2 ^ M)) M u
      | .nan .. => 0 :=
  toFixed_eq FmtOk.b32 x u M rm

theorem toFixed_eq_b64 (x : Bits .b64) (u : Bool) (M : Nat) (rm : Mode) :
    IEEE.toFixed .b64 x u M rm.asl = match Model.exactValue (toM .b64 FmtOk.b64 x) with
      | .finite d => satQ (Model.roundDyadicToInt rm d) M u
      | .infinity s => satQ (signed s (2 ^ M)) M u
      | .nan .. => 0 :=
  toFixed_eq FmtOk.b64 x u M rm

theorem truncInt?_eq_b32 (x : Bits .b32) :
    IEEE.truncInt? .b32 x = match Model.exactValue (toM .b32 FmtOk.b32 x) with
      | .finite d => some (Model.roundDyadicToInt .towardZero d)
      | _ => none :=
  truncInt?_eq FmtOk.b32 x

theorem truncInt?_eq_b64 (x : Bits .b64) :
    IEEE.truncInt? .b64 x = match Model.exactValue (toM .b64 FmtOk.b64 x) with
      | .finite d => some (Model.roundDyadicToInt .towardZero d)
      | _ => none :=
  truncInt?_eq FmtOk.b64 x

end IEEE.Spec

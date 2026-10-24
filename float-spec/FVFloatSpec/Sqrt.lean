import FVFloatSpec.Basic

/-!
# Square root: `FV/Float` against FloatLib

`IEEE.sqrt` (`FPSqrt`) is FloatLib's `Model.sqrtWithRounding` in every `FPCR` rounding mode.
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

/-! ## `isqrt` is the floor square root -/

private theorem two_sqrt_le (n x : Nat) (hx : 0 < x) : 2 * Nat.sqrt n ≤ x + n / x := by
  have hs := Nat.sqrt_le n
  by_cases h : 2 * Nat.sqrt n ≤ x
  · exact le_trans h (Nat.le_add_right _ _)
  · have : (2 * Nat.sqrt n - x) * x ≤ n := by
      obtain ⟨d, hd⟩ : ∃ d, 2 * Nat.sqrt n = x + d := ⟨2 * Nat.sqrt n - x, by omega⟩
      rw [show 2 * Nat.sqrt n - x = d by omega]
      have : (d : Int) * x ≤ Nat.sqrt n * Nat.sqrt n := by
        have hd' : (2 * Nat.sqrt n : Int) = x + d := by exact_mod_cast hd
        nlinarith [sq_nonneg ((x : Int) - d)]
      have h2 : ((d * x : Nat) : Int) ≤ (n : Int) := by push_cast; exact this.trans (by exact_mod_cast hs)
      exact_mod_cast h2
    have := (Nat.le_div_iff_mul_le hx).2 this
    omega

private theorem div_le_sqrt (n x : Nat) (hx : Nat.sqrt n + 1 ≤ x) : n / x ≤ Nat.sqrt n := by
  have h1 := Nat.lt_succ_sqrt n
  have : n / x < Nat.sqrt n + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ hx)
  omega

private theorem isqrt_go (n : Nat) (hn : 0 < n) :
    ∀ fuel x, Nat.sqrt n ≤ x → x - Nat.sqrt n < 2 ^ fuel → isqrt.go fuel n x = Nat.sqrt n := by
  intro fuel
  induction fuel with
  | zero => intro x h1 h2; simp at h2; simp [isqrt.go]; omega
  | succ fuel ih =>
    intro x h1 h2
    have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
    have hx : 0 < x := by omega
    have hy := two_sqrt_le n x hx
    simp only [isqrt.go]
    split
    · rename_i hlt
      have hx1 : Nat.sqrt n + 1 ≤ x := by omega
      have := div_le_sqrt n x hx1
      rw [pow_succ] at h2
      exact ih _ (by omega) (by omega)
    · rename_i hge
      by_contra hne
      have hx1 : Nat.sqrt n + 1 ≤ x := by omega
      have := div_le_sqrt n x hx1
      omega

private theorem isqrt_eq (n : Nat) : isqrt n = Nat.sqrt n := by
  unfold isqrt
  split
  · subst_vars; rfl
  · rename_i hn
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    apply isqrt_go n hn'
    · apply Nat.le_of_lt
      rw [Nat.sqrt_lt]
      calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
        _ ≤ 2 ^ (n.log2 / 2 + 1) * 2 ^ (n.log2 / 2 + 1) := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    · have : 2 ^ (n.log2 / 2 + 1) < 2 ^ (n.log2 + 4) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      exact lt_of_le_of_lt (Nat.sub_le _ _) this

/-! ## Extended mantissas (Lean's unpacked float model) -/

section Ext
open Float.Model.UnpackedFloat

private theorem ext_shr_succ (em : ExtendedMantissa) (k : Nat) :
    em >>> (k + 1) = ExtendedMantissa.shiftRightOne (em >>> k) := rfl

private theorem ext_shr_add (em : ExtendedMantissa) (a b : Nat) :
    em >>> (a + b) = (em >>> a) >>> b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, ext_shr_succ, ih, ext_shr_succ]

private theorem ext_shr_mantissa (em : ExtendedMantissa) (k : Nat) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    rw [ext_shr_succ]
    simp only [ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, pow_succ]

private theorem ofMAA_accuracy (em : ExtendedMantissa) :
    ExtendedMantissa.ofMantissaAndAccuracy em.mantissa em.accuracy = em := by
  obtain ⟨m, r, s⟩ := em
  cases r <;> cases s <;> rfl

/-- An exact mantissa shifted right by `k + 1`: the quotient, the round bit and the sticky bit. -/
private theorem ext_shr_exact (x k : Nat) :
    (⟨x, false, false⟩ : ExtendedMantissa) >>> (k + 1) =
      ⟨x / 2 ^ (k + 1), x / 2 ^ k % 2 != 0, x % 2 ^ k != 0⟩ := by
  induction k with
  | zero =>
    show ExtendedMantissa.shiftRightOne _ = _
    simp [ExtendedMantissa.shiftRightOne, Nat.repeat, Nat.mod_one]
  | succ k ih =>
    rw [ext_shr_succ, ih]
    show ExtendedMantissa.mk _ _ _ = ExtendedMantissa.mk _ _ _
    congr 1
    · rw [Nat.div_div_eq_div_mul, ← pow_succ]
    · show (x / 2 ^ k % 2 != 0 || x % 2 ^ k != 0) = (x % 2 ^ (k + 1) != 0)
      have h := Nat.mod_pow_succ (b := 2) (x := x) (k := k)
      have h2 := Nat.mod_lt (x / 2 ^ k) (by decide : 0 < 2)
      have hp : 0 < 2 ^ k := Nat.two_pow_pos k
      rw [h]
      by_cases h3 : x % 2 ^ k = 0 <;> by_cases h4 : x / 2 ^ k % 2 = 0
      · simp [h3, h4]
      · have h5 : x / 2 ^ k % 2 = 1 := by omega
        simp [h3, h5]
      · simp [h4]
      · have h5 : x / 2 ^ k % 2 = 1 := by omega
        simp [h3, h5]

private theorem log2_div_pow (m j : Nat) (hm : 2 ^ j ≤ m) : (m / 2 ^ j).log2 = m.log2 - j := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos j; omega
  have hq : m / 2 ^ j ≠ 0 := by
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).2 (show 1 * 2 ^ j ≤ m by omega); omega
  have hl : j ≤ m.log2 := (Nat.le_log2 hm0).2 hm
  apply (Nat.log2_eq_iff hq).2
  constructor
  · apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos j)).2
    rw [← pow_add, Nat.sub_add_cancel hl]; exact Nat.log2_self_le hm0
  · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j)).2
    rw [← pow_add, show m.log2 - j + 1 + j = m.log2 + 1 by omega]; exact Nat.lt_log2_self

/-- `roundWithAccuracy` only depends on the extended mantissa at any exponent up to the target. -/
private theorem rwa_shift (spec : Float.Model.Format) (s : Sign) (m : Nat) (e : Int)
    (acc : Accuracy) (j : Nat) (hm : 2 ^ j ≤ m)
    (hj : e + j ≤ spec.targetExponent (Float.Model.totalExponent m e)) :
    roundWithAccuracy spec s m e acc =
      roundWithAccuracy spec s (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> j).mantissa
        (e + j) (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> j).accuracy := by
  have hmant : (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> j).mantissa = m / 2 ^ j := by
    rw [ext_shr_mantissa]; cases acc with
    | exact => rfl
    | inexact o => cases o <;> rfl
  have htot : Float.Model.totalExponent (m / 2 ^ j) (e + j) = Float.Model.totalExponent m e := by
    have hl : j ≤ m.log2 := (Nat.le_log2 (by have := Nat.two_pow_pos j; omega)).2 hm
    simp only [Float.Model.totalExponent, log2_div_pow m j hm]; push_cast [hl]; ring
  have hsh : shiftToTargetExponent spec m e acc =
      shiftToTargetExponent spec (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> j).mantissa
        (e + j) (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> j).accuracy := by
    simp only [shiftToTargetExponent, shiftToExponent, ofMAA_accuracy]
    rw [hmant, htot]
    obtain ⟨t, ht⟩ : ∃ t : Nat, spec.targetExponent (Float.Model.totalExponent m e) = e + j + t :=
      ⟨(spec.targetExponent (Float.Model.totalExponent m e) - (e + j)).toNat, by omega⟩
    rw [ht, show (e + j + t - e).toNat = j + t by omega,
      show (e + j + t - (e + j)).toNat = t by omega, ext_shr_add]
    push_cast; ring_nf
  unfold roundWithAccuracy
  rw [hsh]

end Ext

/-! ## Floor square roots at two scales -/

private theorem sqrt_scaled_eq (N k : Nat) (hR : Nat.sqrt N * Nat.sqrt N = N) :
    Nat.sqrt (N * 4 ^ k) = Nat.sqrt N * 2 ^ k := by
  have h4 : (4 : Nat) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  conv_lhs => rw [h4, ← hR]
  rw [show Nat.sqrt N * Nat.sqrt N * (2 ^ k * 2 ^ k) =
    (Nat.sqrt N * 2 ^ k) * (Nat.sqrt N * 2 ^ k) by ring, Nat.sqrt_eq]

open Float.Model.UnpackedFloat in
/-- The ASL root `isqrt (N * 4^(k+1))`, with its sticky bit folded in as an appended `1`, shifted
back to `N`'s scale, is FloatLib's root of `N` with its accuracy. -/
private theorem sqrt_ext (N k : Nat) :
    (if Nat.sqrt (N * 4 ^ (k + 1)) * Nat.sqrt (N * 4 ^ (k + 1)) = N * 4 ^ (k + 1) then
        (⟨Nat.sqrt (N * 4 ^ (k + 1)), false, false⟩ : ExtendedMantissa) >>> (k + 1)
      else (⟨2 * Nat.sqrt (N * 4 ^ (k + 1)) + 1, false, false⟩ : ExtendedMantissa) >>> (k + 1 + 1)) =
      ExtendedMantissa.ofMantissaAndAccuracy (Nat.sqrt N)
        (Model.ScaledSqrt.accuracy N (Nat.sqrt N)) := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have h4 : (4 : Nat) ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) := by rw [← mul_pow]; norm_num
  have h4' : (4 : Nat) ^ (k + 1) = 4 * (2 ^ k * 2 ^ k) := by rw [h4, pow_succ]; ring
  have hR : Nat.sqrt N = Nat.sqrt (N * 4 ^ (k + 1)) / 2 ^ (k + 1) := by
    rw [← Model.ScaledSqrt.sqrt_div_square, h4,
      Nat.mul_div_cancel _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  have hq : Nat.sqrt (4 * N) = Nat.sqrt (N * 4 ^ (k + 1)) / 2 ^ k := by
    rw [← Model.ScaledSqrt.sqrt_div_square, h4', show N * (4 * (2 ^ k * 2 ^ k)) =
      4 * N * (2 ^ k * 2 ^ k) by ring, Nat.mul_div_cancel _ (Nat.mul_pos hp hp)]
  have hsq : N = Nat.sqrt N * Nat.sqrt N →
      Nat.sqrt (N * 4 ^ (k + 1)) = Nat.sqrt N * 2 ^ (k + 1) := fun h =>
    sqrt_scaled_eq N (k + 1) h.symm
  generalize hn : N * 4 ^ (k + 1) = n at *
  generalize hr : Nat.sqrt n = r at *
  generalize hRR : Nat.sqrt N = R at *
  generalize hqq : Nat.sqrt (4 * N) = q at *
  have hRq : R = q / 2 := by
    rw [hR, hq, Nat.div_div_eq_div_mul, pow_succ]
  have hbit : q % 2 = 1 ↔ R * R + R < N := by
    have : q % 2 = 1 ↔ 2 * R + 1 ≤ q := by omega
    rw [this, ← hqq, Nat.le_sqrt]
    constructor <;> intro h <;> nlinarith
  have hRle : R * R ≤ N := hRR ▸ Nat.sqrt_le N
  have hsplit : r = q * 2 ^ k + r % 2 ^ k := by
    rw [hq]; exact (Nat.div_add_mod' r (2 ^ k)).symm
  have hrR : r / 2 ^ (k + 1) = R := hR.symm
  split
  · rename_i hex
    rw [ext_shr_exact, hrR, ← hq]
    simp only [Model.ScaledSqrt.accuracy]
    by_cases hNR : N = R * R
    · have hr' : r = R * 2 ^ (k + 1) := hsq hNR
      have hmod : r % 2 ^ k = 0 := by
        rw [hr', pow_succ, show R * (2 ^ k * 2) = R * 2 * 2 ^ k by ring, Nat.mul_mod_left]
      have hq0 : ¬ q % 2 = 1 := fun h => by have := hbit.1 h; omega
      simp [hmod, show N - R * R = 0 by omega, ExtendedMantissa.ofMantissaAndAccuracy]
      omega
    · have hmod : r % 2 ^ k ≠ 0 := by
        intro h0
        rw [h0, Nat.add_zero] at hsplit
        have : q * q * (2 ^ k * 2 ^ k) = 4 * N * (2 ^ k * 2 ^ k) :=
          calc q * q * (2 ^ k * 2 ^ k) = (q * 2 ^ k) * (q * 2 ^ k) := by ring
            _ = r * r := by rw [← hsplit]
            _ = N * 4 ^ (k + 1) := by rw [hex, hn]
            _ = 4 * N * (2 ^ k * 2 ^ k) := by rw [h4']; ring
        have hqq' : q * q = 4 * N := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp hp) this
        rcases (show q = 2 * R ∨ q = 2 * R + 1 by omega) with h | h <;> subst h
        · apply hNR; nlinarith
        · have : (2 * R + 1) * (2 * R + 1) = 4 * (R * R + R) + 1 := by ring
          omega
      have hne : N - R * R ≠ 0 := by omega
      by_cases hb : q % 2 = 1
      · have := hbit.1 hb
        simp [hmod, hne, hb, show ¬ N - R * R ≤ R by omega,
          ExtendedMantissa.ofMantissaAndAccuracy]
      · have : ¬ R * R + R < N := fun h => hb (hbit.2 h)
        simp [hmod, hne, show q % 2 = 0 by omega, show N - R * R ≤ R by omega,
          ExtendedMantissa.ofMantissaAndAccuracy]
  · rename_i hex
    rw [ext_shr_exact]
    have hd1 : (2 * r + 1) / 2 ^ (k + 1 + 1) = R := by
      rw [show 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) by ring,
        ← Nat.div_div_eq_div_mul, show (2 * r + 1) / 2 = r by omega, hrR]
    have hd2 : (2 * r + 1) / 2 ^ (k + 1) = q := by
      rw [pow_succ, show 2 ^ k * 2 = 2 * 2 ^ k by ring,
        ← Nat.div_div_eq_div_mul, show (2 * r + 1) / 2 = r by omega, hq]
    have hodd : (2 * r + 1) % 2 ^ (k + 1) ≠ 0 := by
      intro h0
      have := Nat.mod_mod_of_dvd (2 * r + 1) (show 2 ∣ 2 ^ (k + 1) from
        dvd_pow_self 2 (Nat.succ_ne_zero k))
      rw [h0] at this; omega
    have hne : N - R * R ≠ 0 := by
      intro h0
      have hNR : N = R * R := by omega
      apply hex; rw [hsq hNR, ← hn, h4, hNR]; ring
    rw [hd1, hd2]
    simp only [Model.ScaledSqrt.accuracy, hne, ite_false]
    by_cases hb : q % 2 = 1
    · have := hbit.1 hb
      simp [hodd, hb, show ¬ N - R * R ≤ R by omega, ExtendedMantissa.ofMantissaAndAccuracy]
    · have : ¬ R * R + R < N := fun h => hb (hbit.2 h)
      simp [hodd, show q % 2 = 0 by omega, show N - R * R ≤ R by omega,
        ExtendedMantissa.ofMantissaAndAccuracy]

/-! ## Directed rounding of a value known to a finer scale -/

private theorem shr_shr (m a b : Nat) : (m / 2 ^ a).shiftRight b = m.shiftRight (a + b) := by
  show (m / 2 ^ a) >>> b = m >>> (a + b)
  simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]

private theorem magDown_shr (fmt : FloatFormat) (s : Bool) (m : Nat) (e : Int) (j : Nat)
    (hm : 2 ^ (fmt.fracWidth + j) ≤ m) (hl : (m / 2^j).log2 = m.log2 - j) :
    Model.roundDyadicMagnitudeDown fmt s m e =
      Model.roundDyadicMagnitudeDown fmt s (m / 2 ^ j) (e + j) := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos (fmt.fracWidth + j); omega
  have hlj : fmt.fracWidth + j ≤ m.log2 := (Nat.le_log2 hm0).2 hm
  have htot : Int.ofNat (m.log2 - j) + (e + ↑j) = Int.ofNat m.log2 + e := by
    simp only [Int.ofNat_eq_natCast]; push_cast [show j ≤ m.log2 by omega]; ring
  have hnorm : (if m.log2 - j ≥ fmt.fracWidth then (m / 2 ^ j).shiftRight (m.log2 - j - fmt.fracWidth)
        else (m / 2 ^ j).shiftLeft (fmt.fracWidth - (m.log2 - j))) =
      (if m.log2 ≥ fmt.fracWidth then m.shiftRight (m.log2 - fmt.fracWidth)
        else m.shiftLeft (fmt.fracWidth - m.log2)) := by
    rw [ite_eq_left (by omega), ite_eq_left (by omega), shr_shr]; congr 1; omega
  unfold Model.roundDyadicMagnitudeDown
  by_cases h3 : Int.ofNat m.log2 + e < fmt.minNormalExponent
  · have hsub : fmt.minSubnormalExponent = fmt.minNormalExponent - fmt.fracWidth := rfl
    obtain ⟨t, ht⟩ : ∃ t : Nat, e + ↑j - fmt.minSubnormalExponent = Int.negSucc t :=
      ⟨(fmt.minSubnormalExponent - (e + j) - 1).toNat, by
        rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast] at *; omega⟩
    have ht' : e - fmt.minSubnormalExponent = Int.negSucc (j + t) := by
      rw [Int.negSucc_eq] at *; push_cast; omega
    simp only [hl, htot, hnorm]
    simp only [ht, ht', shr_shr, Nat.add_assoc]
  · simp only [hl, htot, hnorm, h3, ite_false]

private theorem ceil_def (n k : Nat) : Model.shiftRightCeilPow2 n k = (n + 2 ^ k - 1) / 2 ^ k := by
  unfold Model.shiftRightCeilPow2
  by_cases hk : k = 0
  · subst hk; simp
  · have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    simp only [hk, beq_iff_eq, ite_false]
    have e1 : n.shiftRight k = n / 2 ^ k := Nat.shiftRight_eq_div_pow n k
    have e2 : ∀ x, x.shiftLeft k = x * 2 ^ k := fun x => Nat.shiftLeft_eq x k
    rw [e1, e2]
    have hmod : n - n / 2 ^ k * 2 ^ k = n % 2 ^ k := by
      have := Nat.div_add_mod' n (2 ^ k); omega
    rw [hmod]
    have hsplit : n + 2 ^ k - 1 = (n % 2 ^ k + 2 ^ k - 1) + n / 2 ^ k * 2 ^ k := by
      have := Nat.div_add_mod' n (2 ^ k); omega
    rw [hsplit, Nat.add_mul_div_right _ _ hp]
    have hlt := Nat.mod_lt n hp
    generalize n % 2 ^ k = r at *
    generalize n / 2 ^ k = q at *
    generalize 2 ^ k = P at *
    split
    · rename_i h0; subst h0; rw [Nat.div_eq_of_lt (by omega)]; simp
    · rename_i h0
      rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; omega

private theorem ceil_ceil (n a b : Nat) :
    Model.shiftRightCeilPow2 (Model.shiftRightCeilPow2 n a) b = Model.shiftRightCeilPow2 n (a + b) := by
  simp only [ceil_def]
  have hA := Nat.two_pow_pos a
  have hB := Nat.two_pow_pos b
  have h1 : (n + 2 ^ a - 1) / 2 ^ a + 2 ^ b - 1 = (n + 2 ^ a - 1 + (2 ^ b - 1) * 2 ^ a) / 2 ^ a := by
    rw [Nat.add_mul_div_right _ _ hA]; generalize (n + 2 ^ a - 1) / 2 ^ a = q; omega
  have h2 : n + 2 ^ a - 1 + (2 ^ b - 1) * 2 ^ a = n + 2 ^ a * 2 ^ b - 1 := by
    have : (2 ^ b - 1) * 2 ^ a + 2 ^ a = 2 ^ a * 2 ^ b := by
      rw [Nat.sub_one_mul, Nat.mul_comm (2 ^ b)]
      have : 2 ^ a ≤ 2 ^ a * 2 ^ b := Nat.le_mul_of_pos_right _ hB
      omega
    have : 2 ^ a ≤ 2 ^ a * 2 ^ b := Nat.le_mul_of_pos_right _ hB
    omega
  rw [h1, h2, Nat.div_div_eq_div_mul, pow_add]

private theorem ceil_pow (a b : Nat) : Model.shiftRightCeilPow2 (2 ^ (a + b)) a = 2 ^ b := by
  rw [ceil_def]
  have hA := Nat.two_pow_pos a
  rw [show 2 ^ (a + b) + 2 ^ a - 1 = (2 ^ a - 1) + 2 ^ b * 2 ^ a by rw [pow_add]; ring_nf; omega,
    Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt (by omega)]
  simp

private theorem ceil_bounds (m j : Nat) (hj : j ≤ m.log2) (hm : m ≠ 0) :
    2 ^ (m.log2 - j) ≤ Model.shiftRightCeilPow2 m j ∧
      Model.shiftRightCeilPow2 m j ≤ 2 ^ (m.log2 - j + 1) := by
  have h1 := Nat.log2_self_le hm
  have h2 := Nat.lt_log2_self (n := m)
  have hA := Nat.two_pow_pos j
  rw [ceil_def]
  constructor
  · apply (Nat.le_div_iff_mul_le hA).2
    rw [← pow_add, Nat.sub_add_cancel hj]; omega
  · apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hA).2
    rw [Nat.succ_mul, ← pow_add, show m.log2 - j + 1 + j = m.log2 + 1 by omega]; omega

private theorem ceil_pow' (k a b : Nat) (h : k = a + b) : Model.shiftRightCeilPow2 (2 ^ k) a = 2 ^ b := by
  subst h; exact ceil_pow a b

private theorem magUp_ceil (fmt : FloatFormat) (s : Bool) (m : Nat) (e : Int) (j : Nat)
    (hm : 2 ^ (fmt.fracWidth + j) ≤ m) :
    Model.roundDyadicMagnitudeUp fmt s m e =
      Model.roundDyadicMagnitudeUp fmt s (Model.shiftRightCeilPow2 m j) (e + j) := by
  have hF := fmt.fracWidth_pos
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos (fmt.fracWidth + j); omega
  have hlj : fmt.fracWidth + j ≤ m.log2 := (Nat.le_log2 hm0).2 hm
  obtain ⟨hc1, hc2⟩ := ceil_bounds m j (by omega) hm0
  have hsub : fmt.minSubnormalExponent = fmt.minNormalExponent - fmt.fracWidth := rfl
  have hNM := Model.minNormalExponent_le_maxNormalExponent fmt
  generalize hc : Model.shiftRightCeilPow2 m j = c at *
  by_cases hcar : c = 2 ^ (m.log2 - j + 1)
  · have hcl : c.log2 = m.log2 - j + 1 := by rw [hcar, Nat.log2_two_pow]
    have htot : Int.ofNat (m.log2 - j + 1) + (e + ↑j) = Int.ofNat m.log2 + e + 1 := by
      simp only [Int.ofNat_eq_natCast]; push_cast [show j ≤ m.log2 by omega]; ring
    have hrm : (if m.log2 ≥ fmt.fracWidth then Model.shiftRightCeilPow2 m (m.log2 - fmt.fracWidth)
        else m.shiftLeft (fmt.fracWidth - m.log2)) = 2 ^ (fmt.fracWidth + 1) := by
      rw [ite_eq_left (by omega), show m.log2 - fmt.fracWidth = j + (m.log2 - j - fmt.fracWidth) by
        omega, ← ceil_ceil, hc, hcar, ceil_pow' _ _ (fmt.fracWidth + 1) (by omega)]
    have hrc : (if m.log2 - j + 1 ≥ fmt.fracWidth then
          Model.shiftRightCeilPow2 c (m.log2 - j + 1 - fmt.fracWidth)
        else c.shiftLeft (fmt.fracWidth - (m.log2 - j + 1))) = 2 ^ fmt.fracWidth := by
      rw [ite_eq_left (by omega), hcar, ceil_pow' _ _ fmt.fracWidth (by omega)]
    have hne : (2 ^ fmt.fracWidth == 2 ^ (fmt.fracWidth + 1)) = false := by
      have := Nat.two_pow_pos fmt.fracWidth
      simp only [beq_eq_false_iff_ne, ne_eq]; rw [pow_succ]; omega
    have hpos : 2 ≤ 2 ^ fmt.fracWidth := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ fmt.fracWidth := Nat.pow_le_pow_right (by decide) hF
    unfold Model.roundDyadicMagnitudeUp Model.packRoundedNormal Model.packRoundedSubnormal
    simp only [hcl, htot, hrm, hrc, Model.pow2_eq_two_pow]
    generalize hT : Int.ofNat m.log2 + e = T
    by_cases A1 : T > fmt.maxNormalExponent
    · simp only [A1, show T + 1 > fmt.maxNormalExponent by omega, ite_true]
    by_cases B1 : T + 1 > fmt.maxNormalExponent
    · simp [A1, B1, show ¬ T < fmt.minSubnormalExponent by omega,
        show ¬ T < fmt.minNormalExponent by omega]
    by_cases B2 : T + 1 < fmt.minSubnormalExponent
    · simp only [A1, B1, B2, show T < fmt.minSubnormalExponent by omega, ite_true, ite_false]
    by_cases A2 : T < fmt.minSubnormalExponent
    · have ht : e + ↑j - fmt.minSubnormalExponent = Int.negSucc (m.log2 - j) := by
        rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast] at hT
        push_cast [show j ≤ m.log2 by omega]; omega
      have h1 : Model.shiftRightCeilPow2 c (m.log2 - j + 1) = 2 ^ 0 := by
        rw [hcar]; exact ceil_pow' _ _ 0 (by omega)
      simp [A1, B1, B2, A2, show T + 1 < fmt.minNormalExponent by omega, ht, h1,
        show ¬ 2 ^ fmt.fracWidth ≤ 1 by omega]
    by_cases A3 : T < fmt.minNormalExponent
    · by_cases B3 : T + 1 < fmt.minNormalExponent
      · obtain ⟨t, ht⟩ : ∃ t : Nat, e + ↑j - fmt.minSubnormalExponent = Int.negSucc t :=
          ⟨(fmt.minSubnormalExponent - (e + j) - 1).toNat, by
            rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast] at *; omega⟩
        have ht' : e - fmt.minSubnormalExponent = Int.negSucc (j + t) := by
          rw [Int.negSucc_eq] at *; push_cast; omega
        simp only [A1, B1, B2, A2, A3, B3, ite_true, ite_false, ht, ht']
        rw [← hc, ceil_ceil, Nat.add_assoc]
      · have ht' : e - fmt.minSubnormalExponent = Int.negSucc (m.log2 - fmt.fracWidth) := by
          rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast] at hT
          push_cast [show fmt.fracWidth ≤ m.log2 by omega]; omega
        have h1 : Model.shiftRightCeilPow2 m (m.log2 - fmt.fracWidth + 1) = 2 ^ fmt.fracWidth := by
          rw [show m.log2 - fmt.fracWidth + 1 = j + (m.log2 - fmt.fracWidth + 1 - j) by omega,
            ← ceil_ceil, hc, hcar, ceil_pow' _ _ fmt.fracWidth (by omega)]
        have hmfe := FloatFormat.maxFiniteExpField_pos fmt
        have hb1 : T + 1 + (fmt.exponentBias : Int) = 1 := by
          have : fmt.minNormalExponent = 1 - Int.ofNat fmt.exponentBias := rfl
          simp only [Int.ofNat_eq_natCast] at this; omega
        have hm1 : ¬ (fmt.maxFiniteExpField : Int) < 1 := by omega
        simp [A1, B1, B2, A2, A3, B3, ht', h1, hne, hb1]
        intro h0; omega
    · simp [A1, B1, B2, A2, A3, show ¬ T + 1 < fmt.minNormalExponent by omega, hne]
  · have hcl : c.log2 = m.log2 - j := by
      apply (Nat.log2_eq_iff (by have := Nat.two_pow_pos (m.log2 - j); omega)).2
      constructor
      · exact hc1
      · omega
    have htot : Int.ofNat (m.log2 - j) + (e + ↑j) = Int.ofNat m.log2 + e := by
      simp only [Int.ofNat_eq_natCast]; push_cast [show j ≤ m.log2 by omega]; ring
    have hnorm : (if m.log2 - j ≥ fmt.fracWidth then
          Model.shiftRightCeilPow2 c (m.log2 - j - fmt.fracWidth)
        else c.shiftLeft (fmt.fracWidth - (m.log2 - j))) =
        (if m.log2 ≥ fmt.fracWidth then Model.shiftRightCeilPow2 m (m.log2 - fmt.fracWidth)
        else m.shiftLeft (fmt.fracWidth - m.log2)) := by
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ← hc, ceil_ceil]; congr 1; omega
    unfold Model.roundDyadicMagnitudeUp
    by_cases h3 : Int.ofNat m.log2 + e < fmt.minNormalExponent
    · obtain ⟨t, ht⟩ : ∃ t : Nat, e + ↑j - fmt.minSubnormalExponent = Int.negSucc t :=
        ⟨(fmt.minSubnormalExponent - (e + j) - 1).toNat, by
          rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast] at *; omega⟩
      have ht' : e - fmt.minSubnormalExponent = Int.negSucc (j + t) := by
        rw [Int.negSucc_eq] at *; push_cast; omega
      simp only [hcl, htot, hnorm]
      simp only [ht, ht']
      rw [← hc, ceil_ceil, Nat.add_assoc]
    · simp only [hcl, htot, hnorm, h3, ite_false]

/-! ## The ASL root as a FloatLib dyadic, against FloatLib's roots -/

section Root
open Float.Model.UnpackedFloat

private theorem ofMAA_mantissa (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

private theorem ofMAA_acc (m : Nat) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).accuracy = acc := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

private theorem ofMAA_inexact (N R : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy R (Model.ScaledSqrt.accuracy N R)).roundBit ||
      (ExtendedMantissa.ofMantissaAndAccuracy R (Model.ScaledSqrt.accuracy N R)).stickyBit) =
      decide (N - R * R ≠ 0) := by
  unfold Model.ScaledSqrt.accuracy
  by_cases h0 : N - R * R = 0
  · simp [h0, ExtendedMantissa.ofMantissaAndAccuracy]
  · by_cases h1 : N - R * R ≤ R <;> simp [h0, h1, ExtendedMantissa.ofMantissaAndAccuracy]

/-- The ASL dyadic (the root, or the root with an appended sticky `1`) is FloatLib's root of `N`
at `k + 1` (or `k + 2`) more places. -/
private theorem root_shift (N k : Nat) (E : Int) : ∃ (r' : Nat) (E'' : Int) (j' : Nat),
    (if Nat.sqrt (N * 4 ^ (k + 1)) * Nat.sqrt (N * 4 ^ (k + 1)) = N * 4 ^ (k + 1) then
        (⟨false, Nat.sqrt (N * 4 ^ (k + 1)), E⟩ : FloatLib.Numerics.Dyadic)
      else ⟨false, 2 * Nat.sqrt (N * 4 ^ (k + 1)) + 1, E - 1⟩) = ⟨false, r', E''⟩ ∧
    E'' + j' = E + (k + 1 : Nat) ∧ 1 ≤ j' ∧
    (⟨r', false, false⟩ : ExtendedMantissa) >>> j' =
      ExtendedMantissa.ofMantissaAndAccuracy (Nat.sqrt N)
        (Model.ScaledSqrt.accuracy N (Nat.sqrt N)) := by
  have := sqrt_ext N k
  split at this
  · rename_i hex
    exact ⟨_, _, k + 1, by rw [if_pos hex], rfl, by omega, this⟩
  · rename_i hex
    exact ⟨_, _, k + 1 + 1, by rw [if_neg hex], by push_cast; ring, by omega, this⟩

private theorem root_div {r' j' N : Nat}
    (hem : (⟨r', false, false⟩ : ExtendedMantissa) >>> j' =
      ExtendedMantissa.ofMantissaAndAccuracy (Nat.sqrt N)
        (Model.ScaledSqrt.accuracy N (Nat.sqrt N))) : r' / 2 ^ j' = Nat.sqrt N := by
  have := congrArg ExtendedMantissa.mantissa hem
  rwa [ext_shr_mantissa, ofMAA_mantissa] at this

private theorem le_of_div_eq {r j R : Nat} (hd : r / 2 ^ j = R) : R * 2 ^ j ≤ r := by
  rw [← hd]; exact Nat.div_mul_le_self r (2 ^ j)

/-- Nearest: FloatLib rounds the ASL dyadic exactly as its root with accuracy. -/
private theorem near_root (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (N k : Nat) (E : Int)
    (hN : 0 < N)
    (hT : E + (k + 1 : Nat) ≤ (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent (Nat.sqrt N) (E + (k + 1 : Nat)))) :
    Model.roundDyadic fmt
      (if Nat.sqrt (N * 4 ^ (k + 1)) * Nat.sqrt (N * 4 ^ (k + 1)) = N * 4 ^ (k + 1) then
        (⟨false, Nat.sqrt (N * 4 ^ (k + 1)), E⟩ : FloatLib.Numerics.Dyadic)
      else ⟨false, 2 * Nat.sqrt (N * 4 ^ (k + 1)) + 1, E - 1⟩) =
      Model.ofModel fmt (roundWithAccuracy (FloatFormat.toModel fmt) .positive (Nat.sqrt N)
        (E + (k + 1 : Nat)) (Model.ScaledSqrt.accuracy N (Nat.sqrt N))) := by
  obtain ⟨r', E'', j', hd, hE, hj, hem⟩ := root_shift N k E
  rw [hd]
  rw [← hE] at hT ⊢
  have hRpos : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.2 hN
  have hdiv := root_div hem
  have hr' : 2 ^ j' ≤ r' := by have := le_of_div_eq hdiv; nlinarith
  have hl : j' ≤ r'.log2 := (Nat.le_log2 (by have := Nat.two_pow_pos j'; omega)).2 hr'
  have htot : Float.Model.totalExponent r' E'' =
      Float.Model.totalExponent (Nat.sqrt N) (E'' + j') := by
    rw [← hdiv]; simp only [Float.Model.totalExponent, log2_div_pow r' j' hr']
    push_cast [hl]; ring
  simp only [Model.roundDyadic, hfmt, ite_true, Model.ieeeRoundDyadic, Model.modelSign_false]
  congr 1
  unfold Float.Model.UnpackedFloat.round decreaseExponent
  have h0 : (E'' - (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent (Nat.sqrt N) (E'' + j'))).toNat = 0 := by omega
  simp only [htot, h0, Nat.shiftLeft_zero, Nat.cast_zero, sub_zero]
  rw [rwa_shift _ _ r' E'' .exact j' hr' (by rw [htot]; exact hT)]
  show roundWithAccuracy _ _ ((⟨r', false, false⟩ : ExtendedMantissa) >>> j').mantissa _
    ((⟨r', false, false⟩ : ExtendedMantissa) >>> j').accuracy = _
  rw [hem, ofMAA_mantissa, ofMAA_acc]

/-- Toward zero / toward −∞: rounding the ASL dyadic down is rounding FloatLib's floor root down. -/
private theorem down_root (fmt : FloatFormat) (rm : Mode)
    (hrm : rm = .towardZero ∨ rm = .towardNegativeInfinity) (N k : Nat) (E : Int)
    (hR : 2 ^ fmt.fracWidth ≤ Nat.sqrt N) :
    Model.roundDyadicWithRounding fmt rm
      (if Nat.sqrt (N * 4 ^ (k + 1)) * Nat.sqrt (N * 4 ^ (k + 1)) = N * 4 ^ (k + 1) then
        (⟨false, Nat.sqrt (N * 4 ^ (k + 1)), E⟩ : FloatLib.Numerics.Dyadic)
      else ⟨false, 2 * Nat.sqrt (N * 4 ^ (k + 1)) + 1, E - 1⟩) =
      Model.roundDyadicDown fmt ⟨false, Nat.sqrt N, E + (k + 1 : Nat)⟩ := by
  obtain ⟨r', E'', j', hd, hE, hj, hem⟩ := root_shift N k E
  rw [hd, ← hE]
  have hdiv := root_div hem
  have hr' : 2 ^ (fmt.fracWidth + j') ≤ r' := by
    have := le_of_div_eq hdiv; rw [pow_add]; nlinarith [Nat.two_pow_pos j']
  have hR0 : Nat.sqrt N ≠ 0 := by have := Nat.two_pow_pos fmt.fracWidth; omega
  have hr0 : r' ≠ 0 := by have := Nat.two_pow_pos (fmt.fracWidth + j'); omega
  have hshr := magDown_shr fmt false r' E'' j' hr'
    (log2_div_pow r' j' (le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hr'))
  rw [hdiv] at hshr
  rcases hrm with rfl | rfl <;>
    simp [Model.roundDyadicWithRounding, Model.roundDyadicTowardZero, Model.roundDyadicDown,
      hr0, hR0, hshr]

private theorem ceil_succ (x k : Nat) : Model.shiftRightCeilPow2 x (k + 1) =
    x / 2 ^ (k + 1) + if x % 2 ^ (k + 1) = 0 then 0 else 1 := by
  rw [ceil_def]
  have hp := Nat.two_pow_pos (k + 1)
  have hsplit : x + 2 ^ (k + 1) - 1 = (x % 2 ^ (k + 1) + 2 ^ (k + 1) - 1) + x / 2 ^ (k + 1) * 2 ^ (k + 1) := by
    have := Nat.div_add_mod' x (2 ^ (k + 1)); omega
  rw [hsplit, Nat.add_mul_div_right _ _ hp]
  have hlt := Nat.mod_lt x hp
  generalize x % 2 ^ (k + 1) = r at *
  generalize x / 2 ^ (k + 1) = q at *
  generalize 2 ^ (k + 1) = P at *
  split
  · rename_i h0; subst h0; rw [Nat.div_eq_of_lt (by omega)]; omega
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; omega

private theorem mod_ne_zero_of_ext (x k : Nat) :
    (((⟨x, false, false⟩ : ExtendedMantissa) >>> (k + 1)).roundBit ||
      ((⟨x, false, false⟩ : ExtendedMantissa) >>> (k + 1)).stickyBit) =
      decide (x % 2 ^ (k + 1) ≠ 0) := by
  rw [ext_shr_exact]
  have h := Nat.mod_pow_succ (b := 2) (x := x) (k := k)
  have h2 := Nat.mod_lt (x / 2 ^ k) (by decide : 0 < 2)
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  show (x / 2 ^ k % 2 != 0 || x % 2 ^ k != 0) = _
  rw [h]
  by_cases h3 : x % 2 ^ k = 0 <;> by_cases h4 : x / 2 ^ k % 2 = 0
  · simp [h3, h4]
  · have h5 : x / 2 ^ k % 2 = 1 := by omega
    simp [h3, h5]
  · simp [h4, h3]
  · have h5 : x / 2 ^ k % 2 = 1 := by omega
    simp [h3, h5]

/-- Toward +∞: rounding the ASL dyadic up is rounding FloatLib's ceiling root up. -/
private theorem up_root (fmt : FloatFormat) (N k : Nat) (E : Int)
    (hR : 2 ^ fmt.fracWidth ≤ Nat.sqrt N) :
    Model.roundDyadicWithRounding fmt .towardPositiveInfinity
      (if Nat.sqrt (N * 4 ^ (k + 1)) * Nat.sqrt (N * 4 ^ (k + 1)) = N * 4 ^ (k + 1) then
        (⟨false, Nat.sqrt (N * 4 ^ (k + 1)), E⟩ : FloatLib.Numerics.Dyadic)
      else ⟨false, 2 * Nat.sqrt (N * 4 ^ (k + 1)) + 1, E - 1⟩) =
      Model.roundDyadicUp fmt ⟨false, if N - Nat.sqrt N * Nat.sqrt N = 0 then Nat.sqrt N
        else Nat.sqrt N + 1, E + (k + 1 : Nat)⟩ := by
  obtain ⟨r', E'', j', hd, hE, hj, hem⟩ := root_shift N k E
  rw [hd, ← hE]
  have hdiv := root_div hem
  have hr' : 2 ^ (fmt.fracWidth + j') ≤ r' := by
    have := le_of_div_eq hdiv; rw [pow_add]; nlinarith [Nat.two_pow_pos j']
  have hr0 : r' ≠ 0 := by have := Nat.two_pow_pos (fmt.fracWidth + j'); omega
  obtain ⟨j0, rfl⟩ : ∃ j0, j' = j0 + 1 := ⟨j' - 1, by omega⟩
  have hceil : Model.shiftRightCeilPow2 r' (j0 + 1) =
      if N - Nat.sqrt N * Nat.sqrt N = 0 then Nat.sqrt N else Nat.sqrt N + 1 := by
    have hb := mod_ne_zero_of_ext r' j0
    rw [hem, ofMAA_inexact] at hb
    rw [ceil_succ, hdiv]
    by_cases h0 : N - Nat.sqrt N * Nat.sqrt N = 0
    · have : r' % 2 ^ (j0 + 1) = 0 := by simp [h0] at hb; omega
      simp [h0, this]
    · have : r' % 2 ^ (j0 + 1) ≠ 0 := by simp [h0] at hb; omega
      simp [h0, this]
  have hshr := magUp_ceil fmt false r' E'' (j0 + 1) hr'
  rw [hceil] at hshr
  have hc0 : (if N - Nat.sqrt N * Nat.sqrt N = 0 then Nat.sqrt N else Nat.sqrt N + 1) ≠ 0 := by
    have := Nat.two_pow_pos fmt.fracWidth; split <;> omega
  simp only [Model.roundDyadicWithRounding, Model.roundDyadicUp]
  simp only [hr0, hc0, beq_iff_eq, ite_false, Bool.false_eq_true, hshr]

end Root

/-! ## FloatLib's square root, case by case -/
/-- FloatLib's square root of a positive finite dyadic in each rounding mode. -/
private def posSqrt (fmt : FloatFormat) : Mode → FloatLib.Numerics.Dyadic → Model fmt
  | .nearestEven, v => Model.FiniteSqrt.sqrtPositiveDyadic fmt v.significand v.exponent
  | .towardPositiveInfinity, v => Model.roundDyadicUp fmt (Model.sqrtDyadicBracket fmt v).upper
  | .towardZero, v => Model.roundDyadicDown fmt (Model.sqrtDyadicBracket fmt v).lower
  | .towardNegativeInfinity, v => Model.roundDyadicDown fmt (Model.sqrtDyadicBracket fmt v).lower

private theorem sqrtWithRounding_eq {fmt : FloatFormat} (rm : Mode) (x : Model fmt) :
    Model.sqrtWithRounding rm x =
      if Model.isNaN x then Model.quietNaN x
      else if Model.isInf x then
        (if Model.signBit x then Model.invalidResult fmt else Model.nativeOverflow fmt false)
      else if Model.isZero x then x
      else if Model.signBit x then Model.invalidResult fmt
      else match Model.toDyadic? x with
        | some v => posSqrt fmt rm v
        | none => Model.invalidResult fmt := by
  cases rm
  case nearestEven =>
    show Model.sqrt x = _
    rw [Model.Proof.sqrt_eq_spec]
    simp only [Model.Spec.sqrt, Model.chooseNaN1]
    by_cases hn : Model.isNaN x <;> simp only [hn, ite_true, ite_false, Bool.false_eq_true]
    cases Model.toDyadic? x <;> rfl
  all_goals
    simp only [Model.sqrtWithRounding, Model.withNaNSelection, Model.chooseNaN1]
    by_cases hn : Model.isNaN x
    · simp [hn]
    · simp only [hn, Bool.false_eq_true, ite_false, dite_true]
      by_cases hi : Model.isInf x
      · simp [hi]
      · have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
          (by simpa using hn) (by simpa using hi)
        cases hv : Model.toDyadic? x with
        | none =>
          have := Model.toDyadic?_isSome_eq_isFinite x
          rw [hv, hfin] at this; simp at this
        | some v =>
          simp [hi, Model.finiteDyadic_eq_of_toDyadic hfin hv, posSqrt]

/-! ## Positive finite operands -/

private theorem log2_sqrt (n : Nat) : (Nat.sqrt n).log2 = n.log2 / 2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hsqrtPos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
  apply (Nat.log2_eq_iff (Nat.ne_of_gt hsqrtPos)).mpr
  constructor
  · rw [Nat.le_sqrt, ← Nat.pow_add]
    calc 2 ^ (n.log2 / 2 + n.log2 / 2) ≤ 2 ^ n.log2 := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n := Nat.log2_self_le hn
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem log2_mul_pow (M s : Nat) (hM : 0 < M) : (M * 2 ^ s).log2 = M.log2 + s := by
  have hp := Nat.two_pow_pos s
  apply (Nat.log2_eq_iff (by positivity)).2
  have h1 := Nat.log2_self_le (n := M) (by omega)
  have h2 := Nat.lt_log2_self (n := M)
  constructor
  · rw [pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show M.log2 + s + 1 = (M.log2 + 1) + s by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 hp

private theorem pow4 (a : Nat) : (4 : Nat) ^ a = 2 ^ (2 * a) := by
  rw [pow_mul]; norm_num

private theorem near_floatlib (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (M : Nat) (e : Int)
    (hM : 0 < M) :
    Model.FiniteSqrt.sqrtPositiveDyadic fmt M e =
      Model.ofModel fmt (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt)
        .positive (Nat.sqrt (M <<< (e - 2 * Min.min (e.ediv 2) ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent M e + 1).ediv 2))).toNat))
        (Min.min (e.ediv 2) ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent M e + 1).ediv 2)))
        (Model.ScaledSqrt.accuracy (M <<< (e - 2 * Min.min (e.ediv 2)
          ((FloatFormat.toModel fmt).targetExponent ((Float.Model.totalExponent M e + 1).ediv 2))).toNat)
          (Nat.sqrt (M <<< (e - 2 * Min.min (e.ediv 2) ((FloatFormat.toModel fmt).targetExponent
            ((Float.Model.totalExponent M e + 1).ediv 2))).toNat)))) := by
  unfold Model.FiniteSqrt.sqrtPositiveDyadic
  simp only [show M ≠ 0 by omega, dite_false, hfmt, ite_true, Model.NativeModelSqrt.sqrt]
  rw [Model.ScaledSqrt.round_eq]

variable {f : Fmt} (h : FmtOk f)

private theorem asl_root (rm : Mode) (n : Nat) (E : Int) (hn : 4 ^ (f.F + 3) ≤ n) :
    IEEE.round f rm.asl false (Nat.sqrt n) E (decide (Nat.sqrt n * Nat.sqrt n ≠ n)) =
      ofM f h (Model.roundDyadicWithRounding (fl f h) rm
        (if Nat.sqrt n * Nat.sqrt n = n then (⟨false, Nat.sqrt n, E⟩ : FloatLib.Numerics.Dyadic)
          else ⟨false, 2 * Nat.sqrt n + 1, E - 1⟩)) := by
  by_cases hex : Nat.sqrt n * Nat.sqrt n = n
  · simp only [hex, ne_eq, not_true_eq_false, decide_false, ite_true]
    exact round_eq h rm false _ E
  · have hr : 2 ^ (f.F + 1) ≤ Nat.sqrt n := by
      have : 2 ^ (f.F + 3) ≤ Nat.sqrt n := Nat.le_sqrt.2 (by rw [← pow_add]; rw [pow4] at hn; convert hn using 2; omega)
      exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) this
    simp only [hex, ne_eq, not_false_eq_true, decide_true, ite_false]
    rw [round_sticky _ false _ E hr]
    exact round_eq h rm false _ _

private theorem pos_core (rm : Mode) (M M' : Nat) (e e' : Int) (hM : 0 < M)
    (hM1 : M < 2 ^ (f.F + 1))
    (hpar : (e % 2 = 0 ∧ M' = M ∧ e' = e) ∨ (e % 2 = 1 ∧ M' = 2 * M ∧ e' = e - 1)) :
    IEEE.round f rm.asl false (Nat.sqrt (M' * 4 ^ (f.F + 3))) (e' / 2 - ((f.F + 3 : Nat) : Int))
      (decide (Nat.sqrt (M' * 4 ^ (f.F + 3)) * Nat.sqrt (M' * 4 ^ (f.F + 3)) ≠
        M' * 4 ^ (f.F + 3))) =
      ofM f h (posSqrt (fl f h) rm ⟨false, M, e⟩) := by
  have hF := h.F1
  have hM' : 0 < M' ∧ M' < 2 ^ (f.F + 2) := by
    rw [pow_succ] at hM1; rw [pow_succ, pow_succ]; omega
  rw [asl_root h rm _ _ (by have := Nat.two_pow_pos (2 * (f.F + 3)); rw [pow4]; nlinarith)]
  congr 1
  have hIEEE : (fl f h).isIEEE = true := by simp [fl]
  have hfw : (fl f h).fracWidth = f.F := rfl
  generalize hE : e' / 2 - ((f.F + 3 : Nat) : Int) = E
  have hed : ∀ x : Int, x.ediv 2 = x / 2 := fun _ => rfl
  cases rm
  case nearestEven =>
    show Model.roundDyadic _ _ = Model.FiniteSqrt.sqrtPositiveDyadic _ M e
    rw [near_floatlib _ hIEEE M e hM]
    generalize hT : Min.min (e.ediv 2) ((FloatFormat.toModel (fl f h)).targetExponent
      ((Float.Model.totalExponent M e + 1).ediv 2)) = T
    have hmb : (FloatFormat.toModel (fl f h)).mantissaBits = 1 + f.F := rfl
    have hTa : T ≤ e / 2 := by rw [← hT, hed]; exact min_le_left _ _
    have hTb : T ≤ (FloatFormat.toModel (fl f h)).targetExponent
        ((Float.Model.totalExponent M e + 1).ediv 2) := by rw [← hT]; exact min_le_right _ _
    have hTc : E + 1 ≤ T := by
      rw [← hT]
      apply le_min
      · rw [hed]; omega
      · simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent, hmb, hed]
        apply le_trans _ (le_max_left _ _)
        omega
    obtain ⟨k, hk⟩ : ∃ k : Nat, T - E = k + 1 := ⟨(T - E - 1).toNat, by omega⟩
    obtain ⟨sh, hsh⟩ : ∃ sh : Nat, e - 2 * T = sh := ⟨(e - 2 * T).toNat, by omega⟩
    rw [hsh, Int.toNat_natCast]
    have hn : M' * 4 ^ (f.F + 3) = (M <<< sh) * 4 ^ (k + 1) := by
      rw [Nat.shiftLeft_eq, pow4, pow4]
      rcases hpar with ⟨hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩
      · rw [mul_assoc, ← pow_add]; congr 2; omega
      · rw [mul_assoc M, ← pow_add, show 2 * M * 2 ^ (2 * (f.F + 3)) = M * 2 ^ (2 * (f.F + 3) + 1) by ring]
        congr 2; omega
    rw [hn]
    have hNpos : 0 < M <<< sh := by rw [Nat.shiftLeft_eq]; positivity
    have hEk : E + ((k + 1 : Nat) : Int) = T := by push_cast; omega
    have htot : Float.Model.totalExponent (Nat.sqrt (M <<< sh)) T =
        (Float.Model.totalExponent M e + 1).ediv 2 := by
      simp only [Float.Model.totalExponent, log2_sqrt, Nat.shiftLeft_eq,
        log2_mul_pow M sh hM, hed]
      push_cast; omega
    have := near_root (fl f h) hIEEE (M <<< sh) k E hNpos (by rw [hEk, htot]; exact hTb)
    rw [hEk] at this
    exact this
  all_goals
    have hbr : Model.sqrtDyadicBracket (fl f h) ⟨false, M, e⟩ =
        ⟨⟨false, Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2))), e' / 2 - ((f.F - M'.log2 / 2 : Nat) : Int)⟩,
         ⟨false, if M' <<< (2 * (f.F - M'.log2 / 2)) - Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2))) *
              Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2))) = 0
            then Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2)))
            else Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2))) + 1,
          e' / 2 - ((f.F - M'.log2 / 2 : Nat) : Int)⟩⟩ := by
      rcases hpar with ⟨hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩
      · simp [Model.sqrtDyadicBracket, hp, hfw]
      · simp [Model.sqrtDyadicBracket, hp, hfw, mul_comm M 2]
    have hl : M'.log2 ≤ f.F + 1 := by
      have := (Nat.log2_lt (by omega)).2 hM'.2; omega
    have hn : M' * 4 ^ (f.F + 3) =
        (M' <<< (2 * (f.F - M'.log2 / 2))) * 4 ^ ((f.F + 2 - (f.F - M'.log2 / 2)) + 1) := by
      rw [Nat.shiftLeft_eq, pow4, pow4, mul_assoc, ← pow_add]; congr 2; omega
    have hEk : E + (((f.F + 2 - (f.F - M'.log2 / 2)) + 1 : Nat) : Int) =
        e' / 2 - ((f.F - M'.log2 / 2 : Nat) : Int) := by
      rw [← hE]; push_cast [show f.F - M'.log2 / 2 ≤ f.F + 2 by omega]; omega
    have hR : 2 ^ (fl f h).fracWidth ≤ Nat.sqrt (M' <<< (2 * (f.F - M'.log2 / 2))) := by
      rw [hfw, Nat.le_sqrt, Nat.shiftLeft_eq, ← pow_add]
      calc 2 ^ (f.F + f.F) ≤ 2 ^ (M'.log2 + 2 * (f.F - M'.log2 / 2)) :=
            Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ M'.log2 * 2 ^ (2 * (f.F - M'.log2 / 2)) := pow_add _ _ _
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le (by omega))
    simp only [posSqrt, hbr]
    rw [hn]
  · rw [down_root _ _ (Or.inl rfl) _ _ _ hR, hEk]
  · rw [up_root _ _ _ _ hR, hEk]
  · rw [down_root _ _ (Or.inr rfl) _ _ _ hR, hEk]

/-! ## Encodings -/

private theorem sq_pack_toNat (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F) :
    (pack f s b fr).toNat = (if s then 2 ^ f.E * 2 ^ f.F else 0) + b * 2 ^ f.F + fr := by
  have h1 : b * 2 ^ f.F + fr < 2 ^ f.E * 2 ^ f.F := by
    have := Nat.mul_le_mul_right (2 ^ f.F) (show b + 1 ≤ 2 ^ f.E by omega)
    rw [Nat.add_mul] at this; omega
  have h2 : (2 : Nat) ^ (1 + f.E + f.F) = 2 * (2 ^ f.E * 2 ^ f.F) := by
    rw [Nat.pow_add, Nat.pow_add]; ring
  simp only [pack, BitVec.toNat_ofNat]
  rw [show (2 : Nat) ^ (f.E + f.F) = 2 ^ f.E * 2 ^ f.F from Nat.pow_add _ _ _, h2]
  rw [Nat.mod_eq_of_lt (by cases s <;> simp <;> omega)]

private theorem sq_expOf_lt (x : Bits f) : expOf f x < 2 ^ f.E := Nat.mod_lt _ (by positivity)
private theorem sq_fracOf_lt (x : Bits f) : fracOf f x < 2 ^ f.F := Nat.mod_lt _ (by positivity)

private theorem sq_bits_eq_pack (x : Bits f) : x = pack f (signOf f x) (expOf f x) (fracOf f x) := by
  apply BitVec.eq_of_toNat_eq
  rw [sq_pack_toNat _ _ _ (sq_expOf_lt x) (sq_fracOf_lt x)]
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


private theorem unpack_sign (x : Bits f) : (unpack f x).2.1 = signOf f x := by
  unfold unpack; simp only; split_ifs <;> rfl

private theorem typeOf_zero (x : Bits f) (hx : typeOf f x = .zero) : x = zero f (signOf f x) := by
  have : expOf f x = 0 ∧ fracOf f x = 0 := by
    revert hx; unfold typeOf unpack; simp only; split_ifs <;> simp_all
  conv_lhs => rw [sq_bits_eq_pack x, this.1, this.2]
  rfl

private theorem unpack_mant (x : Bits f) (hx : typeOf f x = .denormal ∨ typeOf f x = .nonzero) :
    0 < (unpack f x).2.2.1 ∧ (unpack f x).2.2.1 < 2 ^ (f.F + 1) := by
  have := sq_fracOf_lt x
  revert hx; unfold typeOf unpack; simp only; split_ifs <;> simp_all <;> rw [pow_succ] <;> omega

/-! ## Main theorem -/

/-- `FPSqrt` is FloatLib's `sqrtWithRounding` in every `FPCR` rounding mode, on all inputs. -/
theorem sqrt_eq (f : Fmt) (h : FmtOk f) (rm : Mode) (a : Bits f) :
    IEEE.sqrt f rm.asl a = ofM f h (Model.sqrtWithRounding rm (toM f h a)) := by
  have hN := isNaN_toM h a
  have hI := isInf_toM h a
  have hZ := isZero_toM h a
  have hS := signBit_toM h a
  have hD := toDyadic?_toM h a
  have hsg := unpack_sign a
  have hmb := unpack_mant a
  have hz := typeOf_zero a
  have hq := ofM_quietNaN h a
  rw [sqrtWithRounding_eq]
  unfold IEEE.sqrt
  unfold typeOf at hN hI hZ hD hmb hz hq
  generalize unpack f a = u at *
  obtain ⟨t, s, m, e⟩ := u
  simp only at hN hI hZ hD hmb hz hq hsg
  subst hsg
  rw [hN, hI, hZ, hS, hD]
  cases t <;> simp only [FPType.isNaN, reduceCtorEq, decide_false, decide_true, ite_true,
    ite_false, Bool.false_eq_true, false_or, or_false, true_or, or_true, false_and,
    Bool.not_eq_true', ofM_toM, ofM_invalidResult]
  · exact (hz rfl).symm
  · cases hs : signOf f a
    · simp only [Bool.false_eq_true, ite_false]
      obtain ⟨h0, h1⟩ := hmb (Or.inl rfl)
      by_cases he : e % 2 = 0
      · simp only [he, ite_true, isqrt_eq]
        exact pos_core h rm m m e e h0 h1 (Or.inl ⟨he, rfl, rfl⟩)
      · simp only [he, ite_false, isqrt_eq]
        exact pos_core h rm m (2 * m) e (e - 1) h0 h1 (Or.inr ⟨by omega, rfl, rfl⟩)
    · simp [ofM_invalidResult]
  · cases hs : signOf f a
    · simp only [Bool.false_eq_true, ite_false]
      obtain ⟨h0, h1⟩ := hmb (Or.inr rfl)
      by_cases he : e % 2 = 0
      · simp only [he, ite_true, isqrt_eq]
        exact pos_core h rm m m e e h0 h1 (Or.inl ⟨he, rfl, rfl⟩)
      · simp only [he, ite_false, isqrt_eq]
        exact pos_core h rm m (2 * m) e (e - 1) h0 h1 (Or.inr ⟨by omega, rfl, rfl⟩)
    · simp [ofM_invalidResult]
  · cases hs : signOf f a <;> simp [ofM_invalidResult, ofM_nativeOverflow]
  · exact (hq rfl).symm
  · exact (hq rfl).symm

theorem sqrt_eq_b32 (rm : Mode) (a : Bits .b32) :
    IEEE.sqrt .b32 rm.asl a = ofM .b32 FmtOk.b32 (Model.sqrtWithRounding rm (toM .b32 FmtOk.b32 a)) :=
  sqrt_eq .b32 FmtOk.b32 rm a

theorem sqrt_eq_b64 (rm : Mode) (a : Bits .b64) :
    IEEE.sqrt .b64 rm.asl a = ofM .b64 FmtOk.b64 (Model.sqrtWithRounding rm (toM .b64 FmtOk.b64 a)) :=
  sqrt_eq .b64 FmtOk.b64 rm a

end IEEE.Spec

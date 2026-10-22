import FVFloatSpec.Basic
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Core.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
import FloatLib.Numerics.Quantization.Deterministic.ShiftRight

/-!
# Division: `FV/Float` against FloatLib

`IEEE.div` (`FPDiv`) is FloatLib's `Model.divWithRounding` in every `FPCR` rounding mode.
The Arm quotient `q = ⌊m1·2^k / m2⌋` with a sticky remainder bit rounds like the exact dyadic
`(2q+1)·2^(e-1)` (`round_sticky`); FloatLib rounds the exact rational `m1/m2·2^e`. The bridge:
rational rounding only observes the binary exponent and the quotient/remainder class on grids at
least two bits coarser than `q`'s unit, which the sticky dyadic shares; and FloatLib's rational
rounder on a denominator-one rational is its dyadic rounder.
-/

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FSDivAux

open FloatLib.Numerics

private theorem roundQuotientEven_scale_den_one (n p : Nat) :
    let scaled := RationalBinary.scaleByPowerOfTwo n 1 ((p : Int) - n.log2)
    roundQuotientEven scaled.1 scaled.2 =
      if p ≤ n.log2 then roundShiftRightEven n (n.log2 - p)
      else n <<< (p - n.log2) := by
  by_cases h : p ≤ n.log2
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk]
    cases k with
    | zero =>
        simp [RationalBinary.scaleByPowerOfTwo, roundQuotientEven, Nat.mod_one,
          Numerics.roundShiftRightEven_def]
    | succ k =>
        have he : (p : Int) - (p + (k + 1)) = Int.negSucc k := by omega
        simp [he, RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq,
          ← roundShiftRightEven_eq_roundQuotientEven]
  · have he : (p : Int) - n.log2 = Int.ofNat (p - n.log2) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    simp [he, RationalBinary.scaleByPowerOfTwo, roundQuotientEven, Nat.mod_one, h]

/--
Nearest-even quotient rounding of an exact dyadic on a target grid is the shared dyadic shift
primitive.
-/
private theorem roundQuotientEven_scaledDyadic_eq
    (mantissa : Nat) (exponent targetExponent : Int) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        mantissa 1 (exponent - targetExponent)
    roundQuotientEven scaled.1 scaled.2 =
      roundMantissaAtExponentEven mantissa exponent targetExponent := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo
      mantissa 1 (exponent - targetExponent)
  have hdenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      mantissa 1 (exponent - targetExponent) (by decide)
  have hvalue :
      (scaled.1 : Real) / (scaled.2 : Real) =
        (mantissa : Real) * bpow (exponent - targetExponent) := by
    rw [scaleByPowerOfTwo_real]
    simp [scaledRatToReal]
  apply Int.ofNat_inj.mp
  calc
    Int.ofNat (roundQuotientEven scaled.1 scaled.2) =
        FloatLib.Floats.Formats.Flocq.nearestEven
          ((scaled.1 : Real) / (scaled.2 : Real)) :=
      (nearestEven_div_eq_roundQuotientEven scaled.1 scaled.2 hdenominator).symm
    _ = FloatLib.Floats.Formats.Flocq.nearestEven
          ((mantissa : Real) * bpow (exponent - targetExponent)) :=
      congrArg FloatLib.Floats.Formats.Flocq.nearestEven hvalue
    _ = Int.ofNat
          (roundMantissaAtExponentEven mantissa exponent targetExponent) :=
      nearestEven_scaledMagnitude mantissa exponent targetExponent

/--
Floor or ceiling quotient rounding of an exact dyadic on a target grid is the corresponding
directed dyadic shift primitive.
-/
private theorem roundQuotDirected_scaledDyadic_eq
    (roundUp : Bool) (mantissa : Nat) (exponent targetExponent : Int) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        mantissa 1 (exponent - targetExponent)
    roundQuotDirected roundUp scaled.1 scaled.2 =
      if roundUp then
        roundMantissaAtExponentUp mantissa exponent targetExponent
      else
        roundMantissaAtExponentDown mantissa exponent targetExponent := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo
      mantissa 1 (exponent - targetExponent)
  have hdenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      mantissa 1 (exponent - targetExponent) (by decide)
  have hvalue :
      (scaled.1 : Real) / (scaled.2 : Real) =
        (mantissa : Real) * bpow (exponent - targetExponent) := by
    rw [scaleByPowerOfTwo_real]
    simp [scaledRatToReal]
  cases roundUp
  · simp only [roundQuotDirected, Bool.false_eq_true, ite_false]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (scaled.1 / scaled.2) =
          ⌊(scaled.1 : Real) / (scaled.2 : Real)⌋ :=
        (floor_real_nat_div scaled.1 scaled.2).symm
      _ = ⌊(mantissa : Real) * bpow (exponent - targetExponent)⌋ :=
        congrArg Int.floor hvalue
      _ = Int.ofNat
          (roundMantissaAtExponentDown mantissa exponent targetExponent) := by
        simpa [FloatLib.Floats.Formats.Flocq.floorRound] using
          floor_scaledMagnitude mantissa exponent targetExponent
  · simp only [roundQuotDirected, ite_true]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (quotCeil scaled.1 scaled.2) =
          ⌈(scaled.1 : Real) / (scaled.2 : Real)⌉ :=
        (ceil_real_nat_div_eq_quotCeil scaled.1 scaled.2 hdenominator).symm
      _ = ⌈(mantissa : Real) * bpow (exponent - targetExponent)⌉ :=
        congrArg Int.ceil hvalue
      _ = Int.ofNat
          (roundMantissaAtExponentUp mantissa exponent targetExponent) := by
        simpa [FloatLib.Floats.Formats.Flocq.ceilRound] using
          ceil_scaledMagnitude mantissa exponent targetExponent

/-- The policy engine's subnormal shift is the distance to the least-subnormal exponent. -/
private theorem exponent_add_subnormalAlign
    (fmt : FloatFormat) (exponent : Int) :
    exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
      exponent - fmt.minSubnormalExponent := by
  have := fmt.exponentBias_pos
  unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Exponent alignment by nearest-even rounding has the branch form used by the dyadic rounder. -/
private theorem roundMantissaAtExponentEven_eq_match
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentEven mantissa exponent targetExponent =
      match exponent - targetExponent with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => roundShiftRightEven mantissa (shift + 1) := by
  cases hdiff : exponent - targetExponent with
  | ofNat shift =>
      cases shift with
      | zero =>
          have heq : exponent = targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentEven, Numerics.roundShiftRightEven_def, heq]
      | succ shift =>
          have hnot : ¬exponent ≤ targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentEven, hnot, hdiff]
  | negSucc shift =>
      have hle : exponent ≤ targetExponent := by
        omega
      have htoNat : (targetExponent - exponent).toNat = shift + 1 := by
        have hpos : targetExponent - exponent = Int.ofNat (shift + 1) := by
          norm_num at hdiff ⊢
          omega
        rw [hpos]
        rfl
      simp [roundMantissaAtExponentEven, hle, htoNat]

/-- A dyadic strictly below half the target unit rounds to zero under nearest-even. -/
private theorem roundMantissaAtExponentEven_eq_zero_of_far_below
    (mantissa : Nat) (exponent targetExponent : Int)
    (hfar : Int.ofNat mantissa.log2 + exponent + 1 < targetExponent) :
    roundMantissaAtExponentEven mantissa exponent targetExponent = 0 := by
  have hlogNonnegative : 0 ≤ Int.ofNat mantissa.log2 :=
    Int.natCast_nonneg mantissa.log2
  have hexponent : exponent < targetExponent := by
    omega
  let shift := (targetExponent - exponent).toNat
  have hshiftInt : (shift : Int) = targetExponent - exponent := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hexponent.le)
  have hshiftPos : 0 < shift := by
    exact Int.pos_iff_toNat_pos.mp (sub_pos.mpr hexponent)
  have hlogShift : mantissa.log2 + 1 ≤ shift - 1 := by
    have hlogShiftInt :
        Int.ofNat (mantissa.log2 + 1) < Int.ofNat shift := by
      change Int.ofNat mantissa.log2 + 1 < (shift : Int)
      rw [hshiftInt]
      omega
    have hlogShiftNat : mantissa.log2 + 1 < shift := by
      exact Int.ofNat_lt.mp hlogShiftInt
    omega
  have hmantissa :
      mantissa < pow2 (shift - 1) := by
    have hpow :
        2 ^ (mantissa.log2 + 1) ≤ 2 ^ (shift - 1) :=
      Nat.pow_le_pow_right (by decide) hlogShift
    simpa [pow2_eq_two_pow] using
      (Nat.lt_log2_self (n := mantissa)).trans_le hpow
  unfold roundMantissaAtExponentEven
  rw [ite_eq_left hexponent.le]
  exact roundShiftRightEven_eq_zero_of_lt_half
    mantissa shift hshiftPos hmantissa

/-- The rational directed packer at denominator one is the dyadic magnitude packer. -/
private theorem roundRatMagnitudeDirectedScaled_dyadic_eq
    (fmt : FloatFormat) (roundUp sign : Bool) (mantissa : Nat) (exponent : Int) :
    roundRatMagnitudeDirectedScaled fmt roundUp sign mantissa 1 exponent =
      if mantissa = 0 then
        zero fmt sign
      else if roundUp then
        roundDyadicMagnitudeUp fmt sign mantissa exponent
      else
        roundDyadicMagnitudeDown fmt sign mantissa exponent := by
  by_cases hmantissa : mantissa = 0
  · simp [roundRatMagnitudeDirectedScaled, hmantissa]
  · rw [ite_eq_right hmantissa]
    have halign :
        exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
          exponent - fmt.minSubnormalExponent :=
      exponent_add_subnormalAlign fmt exponent
    have hsubnormalDown :
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 =
          roundMantissaAtExponentDown
            mantissa exponent fmt.minSubnormalExponent := by
      rw [halign]
      simpa using
        roundQuotDirected_scaledDyadic_eq
          false mantissa exponent fmt.minSubnormalExponent
    have hsubnormalUp :
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 =
          roundMantissaAtExponentUp
            mantissa exponent fmt.minSubnormalExponent := by
      rw [halign]
      simpa using
        roundQuotDirected_scaledDyadic_eq
          true mantissa exponent fmt.minSubnormalExponent
    have hnormalDown :
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
          roundMantissaToLeadingBitDown mantissa fmt.fracWidth := by
      calc
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
            roundMantissaAtExponentDown mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) := by
          rw [show Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 =
              exponent -
                (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) by
            ring]
          simpa using
            roundQuotDirected_scaledDyadic_eq false mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth)
        _ = roundMantissaToLeadingBitDown mantissa fmt.fracWidth :=
          roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown
            mantissa fmt.fracWidth exponent
    have hnormalUp :
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
          roundMantissaToLeadingBitUp mantissa fmt.fracWidth := by
      calc
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
            roundMantissaAtExponentUp mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) := by
          rw [show Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 =
              exponent -
                (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) by
            ring]
          simpa using
            roundQuotDirected_scaledDyadic_eq true mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth)
        _ = roundMantissaToLeadingBitUp mantissa fmt.fracWidth :=
          roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp
            mantissa fmt.fracWidth exponent
    cases roundUp
    · simp only [Bool.false_eq_true, ite_false]
      unfold roundRatMagnitudeDirectedScaled roundDyadicMagnitudeDown
      simp only [Nat.one_ne_zero, beq_iff_eq, hmantissa, ite_false,
        floorLog2_den_one mantissa hmantissa, ← Int.ofNat_eq_natCast]
      by_cases hoverflow :
          fmt.maxNormalExponent < Int.ofNat mantissa.log2 + exponent
      · simp only [ite_eq_left hoverflow, directedOverflow, Bool.false_eq_true,
          ite_false]
      · simp only [ite_eq_right hoverflow]
        by_cases hunderflow :
            Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent
        · simp only [ite_eq_left hunderflow, Bool.false_eq_true, ite_false]
        · simp only [ite_eq_right hunderflow]
          by_cases hsubnormal :
              Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent
          · have hlt :=
              roundMantissaAtExponentDown_minSubnormal_lt_pow2
                fmt mantissa exponent hsubnormal
            rw [roundMantissaAtExponentDown_eq_match] at hlt
            rw [ite_eq_left hsubnormal, hsubnormalDown,
              roundMantissaAtExponentDown_eq_match]
            simp only [packRoundedSubnormal, beq_iff_eq, not_le_of_gt hlt,
              ite_false, ite_eq_left hsubnormal]
            rfl
          · have hcarry :
                roundMantissaToLeadingBitDown mantissa fmt.fracWidth ≠
                  pow2 (fmt.fracWidth + 1) :=
              ne_of_lt
                (roundMantissaToLeadingBitDown_lt_pow2_succ
                  mantissa fmt.fracWidth)
            rw [ite_eq_right hsubnormal, hnormalDown]
            rw [ite_eq_right hsubnormal]
            unfold packRoundedNormal
            simp only [beq_iff_eq, hcarry, ite_false]
            rw [ite_eq_right hoverflow]
            simp only [roundMantissaToLeadingBitDown, directedOverflow,
              Bool.false_eq_true, ite_false]
            by_cases hleading : fmt.fracWidth ≤ mantissa.log2 <;>
              simp [hleading]
    · simp only [ite_true]
      unfold roundRatMagnitudeDirectedScaled roundDyadicMagnitudeUp
      simp only [Nat.one_ne_zero, beq_iff_eq, hmantissa, ite_false,
        floorLog2_den_one mantissa hmantissa, ← Int.ofNat_eq_natCast]
      by_cases hoverflow :
          fmt.maxNormalExponent < Int.ofNat mantissa.log2 + exponent
      · simp only [ite_eq_left hoverflow, directedOverflow, ite_true]
      · simp only [ite_eq_right hoverflow]
        by_cases hunderflow :
            Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent
        · simp only [ite_eq_left hunderflow]
          cases sign <;>
            simp only [Bool.false_eq_true, ite_false, ite_true,
              posMinSubnormal_eq_ofFields, negMinSubnormal_eq_ofFields]
        · simp only [ite_eq_right hunderflow]
          by_cases hsubnormal :
              Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent
          · have hrounded :
                roundMantissaAtExponentUp
                    mantissa exponent fmt.minSubnormalExponent ≠ 0 :=
              roundMantissaAtExponentUp_ne_zero
                mantissa exponent fmt.minSubnormalExponent hmantissa
            have hmatchNe :
                (match exponent - fmt.minSubnormalExponent with
                  | .ofNat shift => Nat.shiftLeft mantissa shift
                  | .negSucc shift => shiftRightCeilPow2 mantissa (shift + 1)) ≠ 0 := by
              intro hzero
              apply hrounded
              rw [roundMantissaAtExponentUp_eq_match]
              exact hzero
            rw [ite_eq_left hsubnormal, hsubnormalUp,
              roundMantissaAtExponentUp_eq_match]
            simp only [packRoundedSubnormal, beq_iff_eq, ite_eq_left hsubnormal]
            cases hdiff : exponent - fmt.minSubnormalExponent <;>
              simp_all
          · rw [ite_eq_right hsubnormal, hnormalUp]
            simp only [directedOverflow, ite_true, ite_eq_right hsubnormal]
            rfl


private theorem roundQuotientEven_le_of_lt (a b c : Nat) (hb : b ≠ 0) (h : a < c * b) :
    roundQuotientEven a b ≤ c := by
  have hq : a / b < c := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hb)).2 h
  simp only [roundQuotientEven]
  split_ifs <;> omega

/-- A scaled denominator-one pair below `2^p`. -/
private theorem scaled_den_one_lt (n : Nat) (u : Int) (p : Nat)
    (h : (n.log2 : Int) + 1 + u ≤ p) :
    (RationalBinary.scaleByPowerOfTwo n 1 u).1 < 2 ^ p * (RationalBinary.scaleByPowerOfTwo n 1 u).2 := by
  have hlt : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  cases u with
  | ofNat k =>
    show n <<< k < 2 ^ p * 1
    rw [Nat.shiftLeft_eq, Nat.mul_one]
    have : n.log2 + 1 + k ≤ p := by simp at h; omega
    calc n * 2 ^ k < 2 ^ (n.log2 + 1) * 2 ^ k := by
          exact Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 2 ^ (n.log2 + 1 + k) := by rw [Nat.pow_add 2 (n.log2 + 1) k]
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) this
  | negSucc k =>
    show n < 2 ^ p * (1 <<< (k + 1))
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    have : n.log2 + 1 ≤ p + (k + 1) := by simp [Int.negSucc_eq] at h; omega
    calc n < 2 ^ (n.log2 + 1) := hlt
      _ ≤ 2 ^ (p + (k + 1)) := Nat.pow_le_pow_right (by decide) this
      _ = 2 ^ p * 2 ^ (k + 1) := by rw [Nat.pow_add]

private theorem decLe_match_eq {α : Sort _} (P F : Nat) (hb : F ≤ P) (A B : α) :
    (match Nat.decLe P F with
      | isTrue _ => A
      | isFalse _ => B) = if F = P then A else B := by
  generalize Nat.decLe P F = d
  cases d with
  | isFalse h' => simp only; rw [if_neg (by omega)]
  | isTrue h' => simp only; rw [if_pos (by omega)]

private theorem shiftLeft_eq' (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

/-- FloatLib's nearest-even rational rounder at denominator one is its dyadic rounder. -/
private theorem ieeeRoundRatScaled_den_one (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool)
    (n : Nat) (hn : n ≠ 0) (exponent : Int) :
    ieeeRoundRatScaled fmt sign n 1 exponent hfmt =
      roundDyadic fmt { negative := sign, significand := n, exponent := exponent } := by
  have hbias : fmt.exponentBias = fmt.bias := by
    simp [FloatFormat.isIEEE] at hfmt; exact hfmt.2
  have halign : FloatFormat.subnormalAlignExp fmt = FloatFormat.ieeeSubnormalAlignExp fmt := by
    simp [FloatFormat.subnormalAlignExp, FloatFormat.ieeeSubnormalAlignExp, hbias]
  have hN : roundQuotientEven (RationalBinary.scaleByPowerOfTwo n 1 (Int.ofNat fmt.fracWidth - ↑n.log2)).1
      (RationalBinary.scaleByPowerOfTwo n 1 (Int.ofNat fmt.fracWidth - ↑n.log2)).2 =
      if fmt.fracWidth ≤ n.log2 then roundShiftRightEven n (n.log2 - fmt.fracWidth)
      else n <<< (fmt.fracWidth - n.log2) := by
    simpa using roundQuotientEven_scale_den_one n fmt.fracWidth
  have hS : roundQuotientEven
      (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).1
      (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).2 =
      roundMantissaAtExponentEven n exponent (-Int.ofNat fmt.subnormalAlignExp) := by
    have := roundQuotientEven_scaledDyadic_eq n exponent (-Int.ofNat fmt.subnormalAlignExp)
    simpa only [sub_neg_eq_add] using this
  have hSb : (n.log2 : Int) + exponent < FloatFormat.ieeeMinNormalExponent fmt →
      roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).1
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).2
        ≤ pow2 fmt.fracWidth := by
    intro hT
    rw [pow2_eq_two_pow]
    apply roundQuotientEven_le_of_lt _ _ _
      (RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _ (by decide))
    apply scaled_den_one_lt n
    have := fmt.exponentBias_pos
    have := fmt.fracWidth_pos
    simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.subnormalAlignExp, hbias] at hT ⊢
    simp only [Int.ofNat_eq_natCast] at hT ⊢
    omega
  have hS0 : (n.log2 : Int) + exponent < -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt) →
      roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).1
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).2
        = 0 := by
    intro hT
    rw [hS]
    apply roundMantissaAtExponentEven_eq_zero_of_far_below
    have := fmt.exponentBias_pos
    have := fmt.fracWidth_pos
    simp only [FloatFormat.normalMantissaExpOffset, FloatFormat.subnormalAlignExp] at hT ⊢
    simp only [Int.ofNat_eq_natCast] at hT ⊢
    omega
  have hmm : FloatFormat.ieeeMinNormalExponent fmt ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    have := fmt.bias_pos
    simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.ieeeMaxNormalExponent, Int.ofNat_eq_natCast]
    omega
  have hum : -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt) < FloatFormat.ieeeMinNormalExponent fmt := by
    have := fmt.fracWidth_pos
    simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.normalMantissaExpOffset, hbias,
      Int.ofNat_eq_natCast]
    omega
  -- the subnormal fraction, in the dyadic rounder's form
  obtain ⟨Fv, hFv, hFvR⟩ : ∃ Fv, roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).1
        (RationalBinary.scaleByPowerOfTwo n 1 (exponent + Int.ofNat fmt.subnormalAlignExp)).2 = Fv ∧
      (match exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with
        | .ofNat shift => n <<< shift
        | .negSucc shift => roundShiftRightEven n (shift + 1)) = Fv := ⟨_, rfl, by
    rw [hS, roundMantissaAtExponentEven_eq_match, sub_neg_eq_add, halign]; rfl⟩
  rw [hFv] at hSb hS0
  rw [roundDyadic, ite_eq_left hfmt, ieeeRoundDyadic_eq_ieeeRoundDyadicImpl]
  simp only [ieeeRoundRatScaled, ieeeRoundDyadicImpl, beq_iff_eq, hn, Nat.one_ne_zero, ite_false,
    floorLog2_den_one n hn, hN, hFv]
  generalize (if fmt.fracWidth ≤ n.log2 then roundShiftRightEven n (n.log2 - fmt.fracWidth)
      else n <<< (fmt.fracWidth - n.log2)) = Nm
  by_cases h1 : (n.log2 : Int) + exponent > Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)
  · rw [if_pos h1, if_neg (show ¬ ((n.log2 : Int) + exponent < FloatFormat.ieeeMinNormalExponent fmt) by omega)]
    split_ifs <;> first | rfl | omega
  rw [if_neg h1]
  by_cases h3 : (n.log2 : Int) + exponent < FloatFormat.ieeeMinNormalExponent fmt
  · rw [if_pos h3, if_pos h3]
    have hb := hSb h3
    have hRw : ∀ X : Nat, X = Fv → ∀ (A : Model fmt) (B : Nat → Model fmt),
        (if X = 0 then A else if X = pow2 fmt.fracWidth then ofFields fmt sign 1 0 else B X) =
        (if Fv = 0 then A else if Fv = pow2 fmt.fracWidth then ofFields fmt sign 1 0 else B Fv) := by
      rintro X rfl A B; rfl
    rcases hu : exponent + Int.ofNat (FloatFormat.ieeeSubnormalAlignExp fmt) with k | k <;>
      simp only [hu] at hFvR ⊢ <;>
      rw [hRw _ hFvR (if sign = true then negZero fmt else posZero fmt) (ofFields fmt sign 0)]
    all_goals
      by_cases h2 : (n.log2 : Int) + exponent < -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt)
      · rw [if_pos h2, if_pos (hS0 h2)]
      rw [if_neg h2]
      by_cases hz : Fv = 0
      · rw [if_pos hz, if_pos hz]
      rw [if_neg hz, if_neg hz]
      split
      · rename_i hr _
        rw [hFv] at hr
        rw [if_pos (by omega)]
      · rename_i hr _
        rw [hFv] at hr
        rw [if_neg (by omega)]
  · rw [if_neg h3, if_neg h3, if_neg (show ¬ ((n.log2 : Int) + exponent <
      -Int.ofNat (FloatFormat.normalMantissaExpOffset fmt)) by omega)]

/-- FloatLib's rational rounder at denominator one is its dyadic rounder, in every direction. -/
private theorem roundRatWithRoundingScaled_den_one (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (sign : Bool) (n : Nat) (hn : n ≠ 0) (exponent : Int) :
    roundRatWithRoundingScaled fmt mode sign n 1 exponent =
      roundDyadicWithRounding fmt mode
        { negative := sign, significand := n, exponent := exponent } := by
  cases mode with
  | nearestEven =>
    simp only [roundRatWithRoundingScaled, roundRatScaled, dif_pos hfmt, roundDyadicWithRounding]
    exact ieeeRoundRatScaled_den_one fmt hfmt sign n hn exponent
  | towardZero =>
    simp only [roundRatWithRoundingScaled, roundDyadicWithRounding, roundDyadicTowardZero,
      roundRatMagnitudeDirectedScaled_dyadic_eq, hn, beq_iff_eq, ite_false]
    rfl
  | towardPositiveInfinity =>
    cases sign <;>
    simp [roundRatWithRoundingScaled, roundDyadicWithRounding, roundDyadicUp,
      roundRatMagnitudeDirectedScaled_dyadic_eq, hn]
  | towardNegativeInfinity =>
    cases sign <;>
    simp [roundRatWithRoundingScaled, roundDyadicWithRounding, roundDyadicDown,
      roundRatMagnitudeDirectedScaled_dyadic_eq, hn]

/-! ## Rational rounding only sees the quotient class -/

/-- What every quotient rounder observes of `num / den`: the floor, exactness, and the
remainder against half the denominator. -/
private def cls (P : Nat × Nat) : Nat × Bool × Ordering :=
  (P.1 / P.2, P.1 % P.2 == 0, Ord.compare (2 * (P.1 % P.2)) P.2)

private theorem cls_eq {P Q : Nat × Nat} (h : cls P = cls Q) :
    P.1 / P.2 = Q.1 / Q.2 ∧ (P.1 % P.2 = 0 ↔ Q.1 % Q.2 = 0) ∧
      (2 * (P.1 % P.2) < P.2 ↔ 2 * (Q.1 % Q.2) < Q.2) ∧
      (P.2 < 2 * (P.1 % P.2) ↔ Q.2 < 2 * (Q.1 % Q.2)) := by
  simp only [cls, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_, ?_⟩
  · simpa using h2
  · rw [← Nat.compare_eq_lt, ← Nat.compare_eq_lt, h3]
  · rw [← Nat.compare_eq_gt, ← Nat.compare_eq_gt, h3]

private theorem roundQuotientEven_congr {P Q : Nat × Nat} (h : cls P = cls Q) :
    roundQuotientEven P.1 P.2 = roundQuotientEven Q.1 Q.2 := by
  obtain ⟨h1, -, h3, h4⟩ := cls_eq h
  simp only [roundQuotientEven, h1]
  by_cases a : 2 * (P.1 % P.2) < P.2
  · rw [if_pos a, if_pos (h3.1 a)]
  · rw [if_neg a, if_neg (fun x => a (h3.2 x))]
    by_cases b : P.2 < 2 * (P.1 % P.2)
    · rw [if_pos b, if_pos (h4.1 b)]
    · rw [if_neg b, if_neg (fun x => b (h4.2 x))]

private theorem roundQuotDirected_congr (up : Bool) {P Q : Nat × Nat} (h : cls P = cls Q)
    (hP : P.2 ≠ 0) (hQ : Q.2 ≠ 0) :
    roundQuotDirected up P.1 P.2 = roundQuotDirected up Q.1 Q.2 := by
  obtain ⟨h1, h2, -, -⟩ := cls_eq h
  cases up
  · simpa [roundQuotDirected] using h1
  · simp only [roundQuotDirected, quotCeil, beq_iff_eq, hP, hQ, ite_false, ite_true, h1]
    by_cases a : P.1 % P.2 = 0
    · rw [if_pos a, if_pos (h2.1 a)]
    · rw [if_neg a, if_neg (fun x => a (h2.2 x))]

private theorem scaled_snd_ne_zero (n d : Nat) (hd : d ≠ 0) (u : Int) :
    (RationalBinary.scaleByPowerOfTwo n d u).2 ≠ 0 :=
  RationalBinary.scaleByPowerOfTwo_snd_ne_zero n d u hd

private theorem directed_congr (fmt : FloatFormat) (up sign : Bool) (n d n' d' : Nat)
    (hn : n ≠ 0) (hd : d ≠ 0) (hn' : n' ≠ 0) (hd' : d' ≠ 0) (E E' : Int)
    (hT : RationalBinary.floorLog2 n d + E = RationalBinary.floorLog2 n' d' + E')
    (hsub : RationalBinary.floorLog2 n d + E < fmt.minNormalExponent →
      cls (RationalBinary.scaleByPowerOfTwo n d (E + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (E' + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))))
    (hnorm : fmt.minNormalExponent ≤ RationalBinary.floorLog2 n d + E →
      cls (RationalBinary.scaleByPowerOfTwo n d (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n d)) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n' d'))) :
    roundRatMagnitudeDirectedScaled fmt up sign n d E =
      roundRatMagnitudeDirectedScaled fmt up sign n' d' E' := by
  unfold roundRatMagnitudeDirectedScaled
  simp only [beq_iff_eq, hd, hn, hd', hn', ite_false]
  rw [← hT]
  split_ifs <;> first
    | rfl
    | rw [roundQuotDirected_congr up (hsub (by assumption)) (scaled_snd_ne_zero _ _ hd _)
        (scaled_snd_ne_zero _ _ hd' _)]
    | rw [roundQuotDirected_congr up (hnorm (by omega)) (scaled_snd_ne_zero _ _ hd _)
        (scaled_snd_ne_zero _ _ hd' _)]

private theorem ieee_congr (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Bool) (n d n' d' : Nat)
    (hn : n ≠ 0) (hd : d ≠ 0) (hn' : n' ≠ 0) (hd' : d' ≠ 0) (E E' : Int)
    (hT : RationalBinary.floorLog2 n d + E = RationalBinary.floorLog2 n' d' + E')
    (hsub : RationalBinary.floorLog2 n d + E < fmt.minNormalExponent →
      cls (RationalBinary.scaleByPowerOfTwo n d (E + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (E' + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))))
    (hnorm : fmt.minNormalExponent ≤ RationalBinary.floorLog2 n d + E →
      cls (RationalBinary.scaleByPowerOfTwo n d (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n d)) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n' d'))) :
    ieeeRoundRatScaled fmt sign n d E hfmt = ieeeRoundRatScaled fmt sign n' d' E' hfmt := by
  have hmin := FloatFormat.minNormalExponent_eq_ieee fmt hfmt
  unfold ieeeRoundRatScaled
  simp only [beq_iff_eq, hd, hn, hd', hn', ite_false, FloatFormat.subnormalAlignExp]
  rw [← hT]
  by_cases hs : RationalBinary.floorLog2 n d + E < fmt.minNormalExponent
  · rw [roundQuotientEven_congr (hsub hs)]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [roundQuotientEven_congr (hnorm (by omega))]
    split_ifs <;> first | rfl | (exfalso; omega)

private theorem rrs_congr (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (sign : Bool) (n d n' d' : Nat)
    (hn : n ≠ 0) (hd : d ≠ 0) (hn' : n' ≠ 0) (hd' : d' ≠ 0) (E E' : Int)
    (hT : RationalBinary.floorLog2 n d + E = RationalBinary.floorLog2 n' d' + E')
    (hsub : RationalBinary.floorLog2 n d + E < fmt.minNormalExponent →
      cls (RationalBinary.scaleByPowerOfTwo n d (E + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (E' + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))))
    (hnorm : fmt.minNormalExponent ≤ RationalBinary.floorLog2 n d + E →
      cls (RationalBinary.scaleByPowerOfTwo n d (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n d)) =
      cls (RationalBinary.scaleByPowerOfTwo n' d' (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n' d'))) :
    roundRatWithRoundingScaled fmt mode sign n d E =
      roundRatWithRoundingScaled fmt mode sign n' d' E' := by
  cases mode with
  | nearestEven =>
    simp only [roundRatWithRoundingScaled, roundRatScaled, dif_pos hfmt]
    exact ieee_congr fmt hfmt sign n d n' d' hn hd hn' hd' E E' hT hsub hnorm
  | _ => exact directed_congr fmt _ sign n d n' d' hn hd hn' hd' E E' hT hsub hnorm

private theorem cls_scale (A B c : Nat) (hc : c ≠ 0) : cls (A * c, B * c) = cls (A, B) := by
  simp only [cls, Nat.mul_div_mul_right A B (Nat.pos_of_ne_zero hc), Nat.mul_mod_mul_right]
  have hcp := Nat.pos_of_ne_zero hc
  congr 2
  · simp [hc]
  · rw [← Nat.mul_assoc]
    rcases Nat.lt_trichotomy (2 * (A % B)) B with h | h | h
    · rw [Nat.compare_eq_lt.2 h, Nat.compare_eq_lt.2 (Nat.mul_lt_mul_of_pos_right h hcp)]
    · rw [Nat.compare_eq_eq.2 h, Nat.compare_eq_eq.2 (by rw [h])]
    · rw [Nat.compare_eq_gt.2 h, Nat.compare_eq_gt.2 (Nat.mul_lt_mul_of_pos_right h hcp)]

/-- The sticky dyadic `(2q+1)/2^(j+1)` has the class of `(q + r/b)/2^j`, `0 < r < b`, `j ≥ 1`. -/
private theorem cls_sticky (q r b j : Nat) (hr : 0 < r) (hrb : r < b) (hj : 1 ≤ j) :
    cls (q * b + r, b * 2 ^ j) = cls (2 * q + 1, 2 ^ (j + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hb : 0 < b := by omega
  have hP : 0 < 2 ^ (i + 1) := by positivity
  set P := 2 ^ (i + 1) with hPdef
  have hP2 : 2 ^ (i + 1 + 1) = 2 * P := by rw [hPdef, Nat.pow_succ]; ring
  -- q = t * P + w, w < P
  have hw := Nat.mod_lt q hP
  have hqd := Nat.div_add_mod q P
  set t := q / P
  set w := q % P
  have hX : q * b + r = (b * P) * t + (w * b + r) := by rw [← hqd]; ring
  have hXl : w * b + r < b * P := by
    have : (w + 1) * b ≤ P * b := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hY : 2 * q + 1 = (2 * P) * t + (2 * w + 1) := by rw [← hqd]; ring
  have hYl : 2 * w + 1 < 2 * P := by omega
  simp only [cls, hP2]
  rw [hX, hY, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hXl, Nat.div_eq_of_lt hYl, Nat.mul_add_mod_self_left,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hXl, Nat.mod_eq_of_lt hYl]
  have hPe : P = 2 * 2 ^ i := by rw [hPdef, Nat.pow_succ]; ring
  congr 2
  · simp; omega
  · -- `2w+1` is odd and `P` even, so `2(2w+1)` vs `2P` never ties
    rcases Nat.lt_or_ge (2 * w + 2) (P + 1) with h | h
    · have h1 : 2 * w + 2 ≤ P := by omega
      have : 2 * (w * b + r) < b * P := by nlinarith
      rw [Nat.compare_eq_lt.2 this, Nat.compare_eq_lt.2 (by omega)]
    · have h1 : P ≤ 2 * w := by omega
      have : b * P < 2 * (w * b + r) := by nlinarith
      rw [Nat.compare_eq_gt.2 this, Nat.compare_eq_gt.2 (by omega)]

/-- A scaled pair at `u ≤ k` has the class of `(a·2^k) / (b·2^(k-u))`. -/
private theorem cls_scaled (a b k : Nat) (u : Int) (hu : u ≤ k) :
    cls (RationalBinary.scaleByPowerOfTwo a b u) = cls (a * 2 ^ k, b * 2 ^ (k - u).toNat) := by
  cases u with
  | ofNat t =>
    have ht : t ≤ k := by simpa using hu
    have hk : (k - Int.ofNat t).toNat = k - t := by simp
    rw [hk]
    show cls (a <<< t, b) = _
    rw [Nat.shiftLeft_eq, show a * 2 ^ k = a * 2 ^ t * 2 ^ (k - t) by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' ht], cls_scale _ _ _ (by positivity)]
  | negSucc t =>
    have hk : (k - Int.negSucc t).toNat = t + 1 + k := by omega
    rw [hk]
    show cls (a, b <<< (t + 1)) = _
    rw [Nat.shiftLeft_eq, show b * 2 ^ (t + 1 + k) = b * 2 ^ (t + 1) * 2 ^ k by
      rw [Nat.mul_assoc, ← Nat.pow_add], cls_scale _ _ _ (by positivity)]

private theorem scaled_neg (M j : Nat) :
    RationalBinary.scaleByPowerOfTwo M 1 (-((j : Int) + 1)) = (M, 2 ^ (j + 1)) := by
  show RationalBinary.scaleByPowerOfTwo M 1 (Int.negSucc j) = _
  simp [RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq]

private theorem floorLog2_quot (a b k : Nat) (ha : a ≠ 0) (hb : b ≠ 0) (hq : 1 ≤ a * 2 ^ k / b) :
    RationalBinary.floorLog2 a b = ((a * 2 ^ k / b).log2 : Int) - k := by
  have h1 := floorLog2_scaleByPowerOfTwo a b (k : Int) ha hb
  rw [RationalBinary.scaleByPowerOfTwo_natCast] at h1
  simp only [shiftLeft_eq'] at h1
  have hn : a * 2 ^ k ≠ 0 := by positivity
  rw [floorLog2_eq_int_log _ _ hn hb] at h1
  have hle : (1 : ℝ) ≤ ((a * 2 ^ k : ℕ) : ℝ) / (b : ℝ) := by
    have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    rw [one_le_div hbpos]
    have : b ≤ a * 2 ^ k := by
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hb)).1 hq
      omega
    exact_mod_cast this
  have hfd : ⌊((a * 2 ^ k : ℕ) : ℝ) / (b : ℝ)⌋₊ = a * 2 ^ k / b := by
    have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · rw [le_div_iff₀ hbpos]; exact_mod_cast Nat.div_mul_le_self _ _
    · rw [div_lt_iff₀ hbpos]
      have : a * 2 ^ k < (a * 2 ^ k / b + 1) * b := by
        rw [Nat.mul_comm (a * 2 ^ k / b + 1)]; exact Nat.lt_mul_div_succ _ (Nat.pos_of_ne_zero hb)
      exact_mod_cast this
  rw [Int.log_of_one_le_right _ hle, hfd, ← Nat.log2_eq_log_two] at h1
  omega

private theorem log2_two_mul_add_one (q : Nat) (hq : q ≠ 0) : (2 * q + 1).log2 = q.log2 + 1 := by
  have h1 : 2 ^ q.log2 ≤ q := Nat.log2_self_le hq
  have h2 : q < 2 ^ (q.log2 + 1) := Nat.lt_log2_self
  apply le_antisymm
  · have : 2 * q + 1 < 2 ^ (q.log2 + 1 + 1) := by rw [Nat.pow_succ]; omega
    have := (Nat.log2_lt (by omega)).2 this
    omega
  · apply (Nat.le_log2 (by omega)).2
    rw [Nat.pow_succ]; omega

private theorem cls_den_one (M : Nat) (v : Int) (hv : v ≤ 0) :
    cls (RationalBinary.scaleByPowerOfTwo M 1 v) = cls (M, 2 ^ (-v).toNat) := by
  have := cls_scaled M 1 0 v (by simpa using hv)
  simpa using this

private theorem rrs_quotient (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (sign : Bool) (a b k : Nat) (ha : a ≠ 0) (hb : b ≠ 0) (E : Int)
    (hq : 2 ^ (fmt.fracWidth + 1) ≤ a * 2 ^ k / b) :
    roundRatWithRoundingScaled fmt mode sign a b E =
      roundDyadicWithRounding fmt mode
        (if a * 2 ^ k % b = 0 then
          { negative := sign, significand := a * 2 ^ k / b, exponent := E - k }
        else
          { negative := sign, significand := 2 * (a * 2 ^ k / b) + 1, exponent := E - k - 1 }) := by
  set q := a * 2 ^ k / b with hqdef
  set r := a * 2 ^ k % b with hrdef
  have hdm : a * 2 ^ k = q * b + r := by rw [hqdef, hrdef, Nat.mul_comm _ b]; exact (Nat.div_add_mod _ _).symm
  have hq0 : q ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by positivity) hq)
  have hlq : fmt.fracWidth + 1 ≤ q.log2 := (Nat.le_log2 hq0).2 hq
  have hfl := floorLog2_quot a b k ha hb (Nat.one_le_iff_ne_zero.2 hq0)
  rw [← hqdef] at hfl
  have hbias := fmt.exponentBias_pos
  have hrb : r < b := Nat.mod_lt _ (Nat.pos_of_ne_zero hb)
  have hX : ∀ u : Int, u + 1 ≤ k →
      cls (RationalBinary.scaleByPowerOfTwo a b u) = cls (q * b + r, b * 2 ^ (k - u).toNat) := by
    intro u hu; rw [cls_scaled a b k u (by omega), hdm]
  split_ifs with hr
  · rw [← roundRatWithRoundingScaled_den_one fmt hfmt mode sign q hq0]
    have hexact : ∀ J : Nat, cls (q * b + r, b * 2 ^ J) = cls (q, 2 ^ J) := by
      intro J; rw [hr, Nat.add_zero, Nat.mul_comm b, cls_scale _ _ _ hb]
    apply rrs_congr fmt hfmt mode sign a b q 1 ha hb hq0 one_ne_zero
    · rw [floorLog2_den_one q hq0]; omega
    · intro hT
      simp only [FloatFormat.minNormalExponent, Int.ofNat_eq_natCast] at hT ⊢
      rw [hX _ (by omega), hexact, cls_den_one _ _ (by omega)]
      congr 3; omega
    · intro _
      simp only [Int.ofNat_eq_natCast]
      rw [floorLog2_den_one q hq0, hX _ (by omega), hexact, cls_den_one _ _ (by omega)]
      congr 3; omega
  · have hM0 : 2 * q + 1 ≠ 0 := by omega
    rw [← roundRatWithRoundingScaled_den_one fmt hfmt mode sign (2 * q + 1) hM0]
    have hst : ∀ J : Nat, 1 ≤ J → cls (q * b + r, b * 2 ^ J) = cls (2 * q + 1, 2 ^ (J + 1)) :=
      fun J hJ => cls_sticky q r b J (by omega) hrb hJ
    have hlog := log2_two_mul_add_one q hq0
    apply rrs_congr fmt hfmt mode sign a b (2 * q + 1) 1 ha hb hM0 one_ne_zero
    · rw [floorLog2_den_one _ hM0, hlog]; push_cast; omega
    · intro hT
      simp only [FloatFormat.minNormalExponent, Int.ofNat_eq_natCast] at hT ⊢
      rw [hX _ (by omega), hst _ (by omega), cls_den_one _ _ (by omega)]
      congr 3; omega
    · intro _
      simp only [Int.ofNat_eq_natCast]
      rw [floorLog2_den_one _ hM0, hlog, hX _ (by push_cast; omega), hst _ (by push_cast; omega),
        cls_den_one _ _ (by push_cast; omega)]
      congr 3; push_cast; omega

private theorem divWR_finite {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) (dx dy : Numerics.Dyadic)
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy)
    (hnx : isNaN x = false) (hny : isNaN y = false) (hix : isInf x = false) (hiy : isInf y = false)
    (hzx : isZero x = decide (dx.significand = 0)) (hzy : isZero y = decide (dy.significand = 0))
    (hsx : signBit x = dx.negative) (hsy : signBit y = dy.negative) :
    divWithRounding mode x y =
      if dy.significand = 0 then
        (if dx.significand = 0 then invalidResult fmt
         else nativeOverflow fmt (Bool.xor dx.negative dy.negative))
      else if dx.significand = 0 then zero fmt (Bool.xor dx.negative dy.negative)
      else roundRatWithRoundingScaled fmt mode (Bool.xor dx.negative dy.negative)
        dx.significand dy.significand (dx.exponent - dy.exponent) := by
  have hc : chooseNaN2 x y = none := (chooseNaN2_eq_none_iff x y).2 ⟨hnx, hny⟩
  cases mode with
  | nearestEven =>
    show div x y = _
    rw [Proof.div_eq_spec]
    simp only [Spec.div, hdx, hdy, beq_iff_eq]
    rfl
  | _ =>
    simp only [divWithRounding, withNaNSelection, hc, hix, hiy, dite_true, Bool.false_eq_true,
      dite_false, hzx, hzy, finiteDyadic_eq_of_toDyadic _ hdx, finiteDyadic_eq_of_toDyadic _ hdy,
      beq_iff_eq, decide_eq_true_eq]
    rw [hsx, hsy]

private theorem divWR_inf {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt)
    (hnx : isNaN x = false) (hny : isNaN y = false) (hinf : isInf x = true ∨ isInf y = true)
    (hdx : isInf x = true → toDyadic? x = none) (hdy : isInf y = true → toDyadic? y = none) :
    divWithRounding mode x y =
      if isInf x then
        (if isInf y then invalidResult fmt else nativeOverflow fmt (signBit x != signBit y))
      else zero fmt (signBit x != signBit y) := by
  have hc : chooseNaN2 x y = none := (chooseNaN2_eq_none_iff x y).2 ⟨hnx, hny⟩
  cases mode with
  | nearestEven =>
    show div x y = _
    rw [Proof.div_eq_spec]
    cases hX : isInf x <;> cases hY : isInf y <;> simp_all [Spec.div, Spec.divSpecial]
  | _ =>
    cases hX : isInf x <;> cases hY : isInf y <;> simp_all [divWithRounding, withNaNSelection]

private theorem divWR_nan {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt) (n : Model fmt)
    (hc : chooseNaN2 x y = some n)
    (hdx : isNaN x = true → toDyadic? x = none) (hdy : isNaN y = true → toDyadic? y = none) :
    divWithRounding mode x y = n := by
  have hnan : isNaN x = true ∨ isNaN y = true := by
    by_contra hne
    simp only [not_or, Bool.not_eq_true] at hne
    rw [(chooseNaN2_eq_none_iff x y).2 hne] at hc
    simp at hc
  cases mode with
  | nearestEven =>
    show div x y = _
    rw [Proof.div_eq_spec]
    rcases hnan with h | h
    · simp [Spec.div, Spec.divSpecial, hdx h, hc]
    · cases hX : toDyadic? x <;> simp [Spec.div, Spec.divSpecial, hdy h, hc, hX]
  | _ =>
    simp [divWithRounding, withNaNSelection, hc]


end FloatLib.Floats.Formats.BinaryInterchange.Model.FSDivAux

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

private theorem div_round {f : Fmt} (h : FmtOk f) (rm : Mode) (s : Bool) (m1 m2 : Nat) (e1 e2 : Int)
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) :
    IEEE.round f rm.asl s (m1 * 2 ^ (f.F + 4 + m2.log2) / m2) (e1 - e2 - ↑(f.F + 4 + m2.log2))
        (decide (m1 * 2 ^ (f.F + 4 + m2.log2) % m2 ≠ 0)) =
      ofM f h (Model.roundRatWithRoundingScaled (fl f h) rm s m1 m2 (e1 - e2)) := by
  set k := f.F + 4 + m2.log2 with hk
  have hfmt : (fl f h).isIEEE = true := by simp [fl]
  have hq : 2 ^ (f.F + 1) ≤ m1 * 2 ^ k / m2 := by
    apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hm2)).2
    have hlt : m2 < 2 ^ (m2.log2 + 1) := Nat.lt_log2_self
    calc 2 ^ (f.F + 1) * m2 ≤ 2 ^ (f.F + 1) * 2 ^ (m2.log2 + 1) :=
          Nat.mul_le_mul_left _ hlt.le
      _ = 2 ^ (f.F + 2 + m2.log2) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ m1 * 2 ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm1)
  rw [Model.FSDivAux.rrs_quotient (fl f h) hfmt rm s m1 m2 k hm1 hm2 (e1 - e2) hq]
  split_ifs with hr
  · rw [show decide (m1 * 2 ^ k % m2 ≠ 0) = false by simp [hr], round_eq h]
  · rw [show decide (m1 * 2 ^ k % m2 ≠ 0) = true by simp [hr], round_sticky _ _ _ _ hq, round_eq h]


private theorem unpack_facts {f : Fmt} (x : Bits f) :
    ((unpack f x).1 = .zero → (unpack f x).2.2.1 = 0) ∧
    ((unpack f x).1 = .denormal ∨ (unpack f x).1 = .nonzero → (unpack f x).2.2.1 ≠ 0) ∧
    (unpack f x).2.1 = signOf f x := by
  simp only [unpack]
  split_ifs <;> simp_all

/-- `FPDiv` is FloatLib's division in every `FPCR` rounding mode, NaN operands included. -/
theorem div_eq (f : Fmt) (h : FmtOk f) (rm : Mode) (a b : Bits f) :
    IEEE.div f rm.asl a b = ofM f h (Model.divWithRounding rm (toM f h a) (toM f h b)) := by
  have hN := chooseNaN2_toM h a b
  have nx := isNaN_toM h a
  have ny := isNaN_toM h b
  have ix := isInf_toM h a
  have iy := isInf_toM h b
  have zx := isZero_toM h a
  have zy := isZero_toM h b
  have sx := signBit_toM h a
  have sy := signBit_toM h b
  have dx := toDyadic?_toM h a
  have dy := toDyadic?_toM h b
  have ua := unpack_facts a
  have ub := unpack_facts b
  unfold IEEE.div
  simp only [typeOf] at *
  rcases hA : unpack f a with ⟨t1, s1, m1, e1⟩
  rcases hB : unpack f b with ⟨t2, s2, m2, e2⟩
  simp only [hA, hB] at *
  obtain ⟨za, nza, rfl⟩ := ua
  obtain ⟨zb, nzb, rfl⟩ := ub
  set x := toM f h a
  set y := toM f h b
  have hxor : Bool.xor (signOf f a) (signOf f b) = (signOf f a != signOf f b) := by
    cases signOf f a <;> cases signOf f b <;> rfl
  cases hp : processNaNs f t1 t2 a b with
  | some r =>
    rw [hp] at hN
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hN
    rw [Model.FSDivAux.divWR_nan rm x y n hn
      (fun h' => by rw [dx, if_pos (Or.inl (by rw [← nx]; exact h'))])
      (fun h' => by rw [dy, if_pos (Or.inl (by rw [← ny]; exact h'))])]
  | none =>
    simp only
    cases t1 <;> cases t2
    all_goals try (exfalso; simp [processNaNs] at hp; done)
    all_goals
      by_cases hinf : x.isInf = true ∨ y.isInf = true
      · rw [Model.FSDivAux.divWR_inf rm x y (by simp_all [FPType.isNaN]) (by simp_all [FPType.isNaN]) hinf
            (fun _ => by simp_all) (fun _ => by simp_all)]
        simp_all [ofM_invalidResult, ofM_nativeOverflow, ofM_zero]
      · first
        | (exfalso; simp_all; done)
        | (rw [Model.FSDivAux.divWR_finite rm x y ⟨signOf f a, m1, e1⟩ ⟨signOf f b, m2, e2⟩
               (by simp_all [FPType.isNaN]) (by simp_all [FPType.isNaN])
               (by simp_all [FPType.isNaN]) (by simp_all [FPType.isNaN]) (by simp_all) (by simp_all)
               (by simp_all) (by simp_all) sx sy]
           simp only [hxor]
           simp only [reduceCtorEq, true_implies, false_implies, or_true,
             or_false, and_self, and_false, false_and, ite_true, ite_false] at za nza zb nzb ⊢
           first
             | (simp [za, zb, ofM_invalidResult]; done)
             | (simp [za, nzb, ofM_zero]; done)
             | (simp [nza, zb, ofM_nativeOverflow]; done)
             | (simp only [nza, nzb, ite_false]; exact div_round h rm _ m1 m2 e1 e2 nza nzb))

theorem div_eq_b32 (rm : Mode) (a b : Bits .b32) :
    IEEE.div .b32 rm.asl a b =
      ofM .b32 FmtOk.b32 (Model.divWithRounding rm (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  div_eq .b32 FmtOk.b32 rm a b

theorem div_eq_b64 (rm : Mode) (a b : Bits .b64) :
    IEEE.div .b64 rm.asl a b =
      ofM .b64 FmtOk.b64 (Model.divWithRounding rm (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  div_eq .b64 FmtOk.b64 rm a b

end IEEE.Spec

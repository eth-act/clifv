import FVFloatSpec.Defs

/-!
# Encodings, classification and rounding: `FV/Float` against FloatLib

Shared lemmas for the operation proofs (`FVFloatSpec.Arith`, …): `toM` preserves the
classification, sign and exact value of `unpack`; FloatLib's constants and field packing are
`FV/Float`'s; FloatLib's NaN selection is `FPProcessNaNs`; and the core rounding theorem
`round_eq`: the Arm `FPRound` of an exact dyadic is FloatLib's `roundDyadicWithRounding`.

The helper lemmas live in `IEEE.Spec.BasicAux` (field decoding `expField_toM`, `fracField_toM`,
`typeOf_eq`, `pack_toNat`, …). `round_eq` goes through one canonical rounder `BasicAux.canon`
(the shape of FloatLib's `roundDyadicGeneral` with a mode-dependent integer rounding `rq`):
`round_eq_canon` proves `FPRound` equal to it region by region (overflow, subnormal, normal,
carry), `roundDyadicWithRounding_eq_canon` proves FloatLib's nearest-even and directed rounders
equal to it.
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

variable {f : Fmt} (h : FmtOk f)


/-! ### Field decoding -/

namespace BasicAux

theorem fl_fracWidth : (fl f h).fracWidth = f.F := rfl

theorem fl_expWidth : (fl f h).expWidth = f.E := rfl

theorem fl_bitWidth : (fl f h).bitWidth = 1 + f.E + f.F := rfl

theorem fl_encoding : (fl f h).encoding = .ieee := rfl

theorem fl_exponentBias : (fl f h).exponentBias = f.bias := rfl

theorem fl_bias : (fl f h).bias = f.bias := rfl

theorem fl_isIEEE : (fl f h).isIEEE = true := FloatFormat.isIEEE_ieee _ _ _ _

theorem fl_supportsSignedZero : (fl f h).supportsSignedZero = true := rfl

theorem toM_bits (x : Bits f) : (toM f h x).bits = x := rfl

theorem ofM_eq (y : Model (fl f h)) : ofM f h y = y.bits := rfl

attribute [local simp] fl_fracWidth fl_expWidth fl_bitWidth fl_encoding fl_exponentBias fl_bias
  fl_isIEEE fl_supportsSignedZero toM_bits

theorem two_pow_E (h : FmtOk f) : 2 ^ f.E = 2 * f.bias + 2 := by
  have := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two (fl f h)
  simpa using this

private theorem testBit_eq_le (n i : Nat) (hn : n < 2 ^ (i + 1)) :
    n.testBit i = decide (2 ^ i ≤ n) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hlt : n / 2 ^ i < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]; rw [Nat.pow_succ] at hn; omega
  by_cases hle : 2 ^ i ≤ n
  · have : 1 ≤ n / 2 ^ i := (Nat.le_div_iff_mul_le hp).2 (by omega)
    simp only [hle, decide_true, decide_eq_true_eq]; omega
  · have : n / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
    simp [hle, this]

private theorem or_low (a b k : Nat) (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt hb a).symm

private theorem or_top (t k : Nat) (ht : t < 2 ^ k) : 2 ^ k ||| t = 2 ^ k + t := by
  simpa using or_low 1 t k ht

theorem toNat_lt (x : Bits f) : x.toNat < 2 ^ (f.E + f.F + 1) := by
  exact Nat.lt_of_lt_of_eq x.isLt (by rw [show 1 + f.E + f.F = f.E + f.F + 1 by omega])

theorem expField_toM (x : Bits f) : Model.expField (toM f h x) = expOf f x := by
  rw [Model.expField_eq_expFieldImpl_apply]
  simp [Model.expFieldImpl, Model.toNatBits, FloatFormat.expAllOnesNat,
    Nat.and_two_pow_sub_one_eq_mod, expOf, Nat.shiftRight_eq_div_pow]

theorem fracField_toM (x : Bits f) : Model.fracField (toM f h x) = fracOf f x := by
  rw [Model.fracField_eq_fracFieldImpl_apply]
  simp [Model.fracFieldImpl, Model.toNatBits, FloatFormat.fracMaskNat,
    Nat.and_two_pow_sub_one_eq_mod, fracOf]

theorem signBit_toM' (x : Bits f) : Model.signBit (toM f h x) = signOf f x := by
  rw [Model.signBit_eq_signBitImpl_apply]
  simp only [Model.signBitImpl, Model.toNatBits, toM_bits, fl_expWidth, fl_fracWidth, signOf]
  exact testBit_eq_le _ _ (toNat_lt x)

theorem expOf_lt (x : Bits f) : expOf f x < 2 ^ f.E := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fracOf_lt (x : Bits f) : fracOf f x < 2 ^ f.F := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The quiet bit of an encoding is the top fraction bit. -/
theorem quietBit_toM (x : Bits f) :
    ((toM f h x).bits &&& FloatFormat.quietBit (fl f h) == 0) =
      decide (fracOf f x < 2 ^ (f.F - 1)) := by
  have hF := h.F1
  have hq : 2 ^ (f.F - 1) < 2 ^ (1 + f.E + f.F) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hbit : x.toNat.testBit (f.F - 1) = decide (2 ^ (f.F - 1) ≤ fracOf f x) := by
    have h1 := Nat.testBit_mod_two_pow x.toNat f.F (f.F - 1)
    simp only [show f.F - 1 < f.F by omega, decide_true, Bool.true_and] at h1
    rw [← h1]
    exact testBit_eq_le _ _ (by rw [show f.F - 1 + 1 = f.F by omega]; exact fracOf_lt x)
  have : ((toM f h x).bits &&& FloatFormat.quietBit (fl f h)).toNat =
      2 ^ (f.F - 1) * (x.toNat.testBit (f.F - 1)).toNat := by
    rw [BitVec.toNat_and]
    show x.toNat &&& (BitVec.ofNat (1 + f.E + f.F) (2 ^ (f.F - 1))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.and_two_pow, Nat.mul_comm]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, this,
    BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, hbit]
  have hp : 0 < 2 ^ (f.F - 1) := Nat.two_pow_pos _
  by_cases hc : 2 ^ (f.F - 1) ≤ fracOf f x <;> simp [hc]; omega

theorem typeOf_eq (x : Bits f) : typeOf f x =
    if expOf f x = 0 then (if fracOf f x = 0 then .zero else .denormal)
    else if expOf f x = f.expOnes then
      (if fracOf f x = 0 then .infinity else if 2 ^ (f.F - 1) ≤ fracOf f x then .qnan else .snan)
    else .nonzero := by
  simp only [typeOf, unpack]; split_ifs <;> rfl

theorem expAllOnesNat_fl : FloatFormat.expAllOnesNat (fl f h) = f.expOnes := rfl

attribute [local simp] expAllOnesNat_fl

theorem expOnes_pos (h : FmtOk f) : 3 ≤ f.expOnes := by
  have := two_pow_E h; have := h.E2
  have : 0 < f.bias := by simpa using FloatFormat.bias_pos (fl f h)
  simp only [Fmt.expOnes]; omega

end BasicAux

open BasicAux

attribute [local simp] fl_fracWidth fl_expWidth fl_bitWidth fl_encoding fl_exponentBias fl_bias
  fl_isIEEE fl_supportsSignedZero toM_bits expAllOnesNat_fl

/-! ## Classification and decoding -/

theorem isNaN_toM (x : Bits f) : Model.isNaN (toM f h x) = (typeOf f x).isNaN := by
  have := expOnes_pos h
  simp only [Model.isNaN, fl_encoding, Model.IEEE.isNaN, expField_toM, fracField_toM,
    expAllOnesNat_fl, typeOf_eq]
  split_ifs <;> simp_all [FPType.isNaN]
  omega

theorem isSNaN_toM (x : Bits f) : Model.isSNaN (toM f h x) = decide (typeOf f x = .snan) := by
  have := expOnes_pos h
  simp only [Model.isSNaN, fl_encoding, Model.IEEE.isSNaN, Model.IEEE.isNaN, expField_toM,
    fracField_toM, expAllOnesNat_fl, quietBit_toM, typeOf_eq]
  split_ifs <;> simp_all
  omega

theorem isInf_toM (x : Bits f) : Model.isInf (toM f h x) = decide (typeOf f x = .infinity) := by
  have := expOnes_pos h
  simp only [Model.isInf, fl_encoding, Model.IEEE.isInf, expField_toM, fracField_toM,
    expAllOnesNat_fl, typeOf_eq]
  split_ifs <;> simp_all <;> omega

theorem isZero_toM (x : Bits f) : Model.isZero (toM f h x) = decide (typeOf f x = .zero) := by
  have := expOnes_pos h
  simp only [Model.isZero, fl_encoding, Model.IEEE.isZero, expField_toM, fracField_toM,
    typeOf_eq]
  split_ifs <;> simp_all

theorem signBit_toM (x : Bits f) : Model.signBit (toM f h x) = signOf f x := by
  exact signBit_toM' h x

/-- Exact decoding: FloatLib's dyadic of a finite encoding is `FPUnpack`'s sign, mantissa and
exponent (zeros: mantissa 0, exponent 0, as in `unpack`). -/
theorem toDyadic?_toM (x : Bits f) :
    Model.toDyadic? (toM f h x) =
      if (typeOf f x).isNaN ∨ typeOf f x = .infinity then none
      else some ⟨(unpack f x).2.1, (unpack f x).2.2.1, (unpack f x).2.2.2⟩ := by
  have := expOnes_pos h
  simp only [Model.toDyadic?, fl_isIEEE, ite_true, Model.ieeeToDyadic?, Model.IEEE.isNaN,
    Model.IEEE.isInf, expField_toM, fracField_toM, signBit_toM', expAllOnesNat_fl, typeOf,
    unpack, Model.pow2_eq_two_pow, FloatFormat.ieeeMinSubnormalExponent,
    FloatFormat.ieeeNormalMantissaExpOffset, fl_fracWidth, fl_bias, Fmt.minExp]
  split_ifs <;> simp_all [FPType.isNaN] <;> omega

/-! ## Constants and packing -/

/-! ### Packing -/

namespace BasicAux

theorem pack_toNat (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F) :
    (pack f s b fr).toNat = (if s then 2 ^ (f.E + f.F) else 0) + b * 2 ^ f.F + fr := by
  have h1 : b * 2 ^ f.F + fr < 2 ^ (f.E + f.F) := by
    rw [Nat.pow_add]
    have : b * 2 ^ f.F + fr < (b + 1) * 2 ^ f.F := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hb)
  have h2 : 2 ^ (f.E + f.F) + (b * 2 ^ f.F + fr) < 2 ^ (1 + f.E + f.F) := by
    rw [show 1 + f.E + f.F = (f.E + f.F) + 1 by omega, Nat.pow_succ]; omega
  unfold pack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  cases s <;> simp <;> omega

/-- Two encodings are equal when their naturals are. -/
theorem bits_eq_pack (y : Bits f) (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F)
    (hy : y.toNat = (if s then 2 ^ (f.E + f.F) else 0) + b * 2 ^ f.F + fr) :
    y = pack f s b fr := by
  apply BitVec.eq_of_toNat_eq; rw [hy, pack_toNat s b fr hb hfr]

theorem signMask_fl : FloatFormat.signMask (fl f h) = BitVec.ofNat _ (2 ^ (f.E + f.F)) := by
  simp only [FloatFormat.signMask, FloatFormat.ofWordNat, FloatFormat.signMaskNat,
    FloatFormat.signBitIndex, fl_bitWidth]
  congr 2; omega

theorem signMask_toNat_fl : (FloatFormat.signMask (fl f h)).toNat = 2 ^ (f.E + f.F) := by
  rw [FloatFormat.signMask_toNat, fl_bitWidth]; congr 1; omega

theorem expMask_toNat :
    (FloatFormat.expMask (fl f h)).toNat = (2 ^ f.E - 1) * 2 ^ f.F := by
  have hlt : (2 ^ f.E - 1) * 2 ^ f.F < 2 ^ (1 + f.E + f.F) := by
    have : (2 ^ f.E - 1) * 2 ^ f.F < 2 ^ f.E * 2 ^ f.F :=
      Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.E; omega) (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [FloatFormat.expMask, FloatFormat.ofWordNat, FloatFormat.expMaskNat,
    FloatFormat.expAllOnesNat, fl_expWidth, fl_fracWidth, fl_bitWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

end BasicAux

open BasicAux

theorem ofM_ofFields (s : Bool) (b fr : Nat) (hb : b < 2 ^ f.E) (hfr : fr < 2 ^ f.F) :
    ofM f h (Model.ofFields (fl f h) s b fr) = pack f s b fr := by
  apply bits_eq_pack _ s b fr hb hfr
  show (Model.mkBits (fl f h) s b fr).toNat = _
  rw [Model.mkBits_eq_mkBitsImpl_apply]
  show ((if s then 1 <<< (f.E + f.F) else 0) |||
      (b &&& (2 ^ f.E - 1)) <<< f.F ||| (fr &&& (2 ^ f.F - 1))) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hfr, Nat.or_assoc, Nat.shiftLeft_eq b, or_low b fr f.F hfr]
  have h1 : b * 2 ^ f.F + fr < 2 ^ (f.E + f.F) := by
    rw [Nat.pow_add]
    have : b * 2 ^ f.F + fr < (b + 1) * 2 ^ f.F := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hb)
  cases s
  · simp
  · simp only [ite_true, Nat.shiftLeft_eq, Nat.one_mul]; rw [or_top _ _ h1]; omega

theorem ofM_zero (s : Bool) : ofM f h (Model.zero (fl f h) s) = zero f s := by
  have hE : 0 < 2 ^ f.E := Nat.two_pow_pos _
  have hF : 0 < 2 ^ f.F := Nat.two_pow_pos _
  apply bits_eq_pack _ s 0 0 hE hF
  have hq : 2 ^ (f.E + f.F) < 2 ^ (1 + f.E + f.F) := Nat.pow_lt_pow_right (by decide) (by omega)
  cases s
  · simp [ofM_eq, Model.zero, Model.posZero, Model.ofNatBits, Model.ofBits, FloatFormat.ofWordNat]
  · simp [ofM_eq, Model.zero, Model.negZero, Model.ofBits, signMask_fl, Nat.mod_eq_of_lt hq]

theorem ofM_nativeOverflow (s : Bool) :
    ofM f h (Model.nativeOverflow (fl f h) s) = infinity f s := by
  have hE : f.expOnes < 2 ^ f.E := by have := Nat.two_pow_pos f.E; simp only [Fmt.expOnes]; omega
  apply bits_eq_pack _ s _ 0 hE (Nat.two_pow_pos _)
  have hlt : (2 ^ f.E - 1) * 2 ^ f.F < 2 ^ (f.E + f.F) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.E; omega) (Nat.two_pow_pos _)
  cases s
  · show (FloatFormat.expMask (fl f h)).toNat = _
    rw [expMask_toNat]; simp [Fmt.expOnes]
  · show (FloatFormat.signMask (fl f h) ||| FloatFormat.expMask (fl f h)).toNat = _
    rw [BitVec.toNat_or, expMask_toNat, signMask_toNat_fl, or_top _ _ hlt]
    simp [Fmt.expOnes]

theorem ofM_maxFinite (s : Bool) : ofM f h (Model.maxFinite (fl f h) s) = maxNormal f s := by
  have := expOnes_pos h
  have hE : f.expOnes < 2 ^ f.E := by have := Nat.two_pow_pos f.E; simp only [Fmt.expOnes]; omega
  have h1 : (fl f h).maxFiniteExpField = f.expOnes - 1 := by
    simp only [FloatFormat.maxFiniteExpField, fl_encoding, fl_expWidth,
      FloatFormat.Encoding.maxFiniteExponent, Fmt.expOnes]; omega
  have h2 : (fl f h).maxFiniteFracField = 2 ^ f.F - 1 := rfl
  unfold Model.maxFinite maxNormal
  rw [h1, h2, ofM_ofFields]
  · omega
  · have := Nat.two_pow_pos f.F; omega

theorem ofM_invalidResult : ofM f h (Model.invalidResult (fl f h)) = defaultNaN f := by
  have hF := h.F1
  have hE : f.expOnes < 2 ^ f.E := by have := Nat.two_pow_pos f.E; simp only [Fmt.expOnes]; omega
  have hq : 2 ^ (f.F - 1) < 2 ^ f.F := Nat.pow_lt_pow_right (by decide) (by omega)
  apply bits_eq_pack _ false _ _ hE hq
  have hq' : 2 ^ (f.F - 1) < 2 ^ (1 + f.E + f.F) := Nat.pow_lt_pow_right (by decide) (by omega)
  show (FloatFormat.expMask (fl f h) ||| FloatFormat.quietBit (fl f h)).toNat = _
  rw [BitVec.toNat_or, expMask_toNat]
  show _ ||| (BitVec.ofNat (1 + f.E + f.F) (2 ^ (f.F - 1))).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq', or_low _ _ _ hq]; simp [Fmt.expOnes]

theorem ofM_neg (x : Bits f) : ofM f h (Model.neg (toM f h x)) = neg f x := by
  simp only [Model.neg, fl_supportsSignedZero, ite_true, Model.toggleSign, Model.ofBits, ofM_eq,
    toM_bits, signMask_fl, neg]
  rfl

/-! ## NaN selection -/

/-! ### Quietening -/

namespace BasicAux

theorem or_quietBit_of_qnan (hF : 0 < f.F) (x : Bits f) (hx : 2 ^ (f.F - 1) ≤ fracOf f x) :
    x ||| BitVec.ofNat _ (2 ^ (f.F - 1)) = x := by
  have hq : 2 ^ (f.F - 1) < 2 ^ (1 + f.E + f.F) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hbit : x.toNat.testBit (f.F - 1) = true := by
    have h1 := Nat.testBit_mod_two_pow x.toNat f.F (f.F - 1)
    simp only [show f.F - 1 < f.F by omega, decide_true, Bool.true_and] at h1
    rw [← h1, testBit_eq_le _ _ (by rw [show f.F - 1 + 1 = f.F by omega]; exact fracOf_lt x)]
    simpa [fracOf] using hx
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : f.F - 1 = i
  · subst hi; simp [hbit]
  · simp [hi]

theorem ofM_quietNaN_eq (x : Bits f) :
    ofM f h (Model.quietNaN (toM f h x)) =
      if (typeOf f x).isNaN then processNaN f (typeOf f x) x else x := by
  have hn := isNaN_toM h x
  simp only [Model.isNaN, fl_encoding] at hn
  simp only [Model.quietNaN, fl_encoding, hn]
  by_cases hN : (typeOf f x).isNaN = true
  · simp only [hN, ite_true, processNaN]
    by_cases hs : typeOf f x = .snan
    · simp [hs]; rfl
    · simp only [hs, ite_false, ofM_eq, Model.ofBits, toM_bits]
      apply or_quietBit_of_qnan h.F1
      have := expOnes_pos h
      rw [typeOf_eq] at hN hs
      split_ifs at hN hs <;> simp_all [FPType.isNaN]
  · simp only [hN]; rfl

end BasicAux

open BasicAux

/-- FloatLib's quietening of a NaN is `FPProcessNaN`. -/
theorem ofM_quietNaN (x : Bits f) (hx : (typeOf f x).isNaN = true) :
    ofM f h (Model.quietNaN (toM f h x)) = processNaN f (typeOf f x) x := by
  rw [ofM_quietNaN_eq, ite_eq_left hx]

theorem chooseNaN1_toM (x : Bits f) :
    (Model.chooseNaN1 (toM f h x)).map (ofM f h) =
      if (typeOf f x).isNaN then some (processNaN f (typeOf f x) x) else none := by
  simp only [Model.chooseNaN1, isNaN_toM]
  split <;> simp_all [ofM_quietNaN_eq]

/-- FloatLib's two-operand NaN selection is `FPProcessNaNs`. -/
theorem chooseNaN2_toM (a b : Bits f) :
    (Model.chooseNaN2 (toM f h a) (toM f h b)).map (ofM f h) =
      processNaNs f (typeOf f a) (typeOf f b) a b := by
  simp only [Model.chooseNaN2, isNaN_toM, isSNaN_toM]
  cases ha : typeOf f a <;> cases hb : typeOf f b <;>
    simp [processNaNs, FPType.isNaN, ofM_quietNaN_eq, ha, hb]

/-- FloatLib's three-operand NaN selection is `FPProcessNaNs3` (same operand order). -/
theorem chooseNaN3_toM (a b c : Bits f) :
    (Model.chooseNaN3 (toM f h a) (toM f h b) (toM f h c)).map (ofM f h) =
      processNaNs3 f (typeOf f a) (typeOf f b) (typeOf f c) a b c := by
  simp only [Model.chooseNaN3, isNaN_toM, isSNaN_toM]
  cases ha : typeOf f a <;> cases hb : typeOf f b <;> cases hc : typeOf f c <;>
    simp [processNaNs3, FPType.isNaN, ofM_quietNaN_eq, ha, hb, hc]

/-! ## Rounding -/

/-! ### `FPRound` and FloatLib's rounders against one canonical rounder -/

namespace BasicAux

/-- `FPRoundBase`'s rounding decision: whether to increment, and whether overflow gives ∞. -/
def aslRU (rm : RMode) (sign : Bool) (intMant : Nat) (err : Err) : Bool × Bool :=
  let inexact := err ≠ .exact
  match rm with
  | .rne => (err = .high ∨ (err = .half ∧ intMant % 2 = 1), true)
  | .rna => (err = .high ∨ err = .half, true)
  | .rpi => (inexact ∧ !sign, !sign)
  | .rmi => (inexact ∧ sign, sign)
  | .rz => (false, false)

/-- `FPRoundBase`'s truncated mantissa and error class. -/
def aslPair (f : Fmt) (mant : Nat) (exp : Int) (sticky : Bool) : Nat × Err :=
  let exponent : Int := (mant.log2 : Int) + exp
  let biased : Int := Max.max (exponent - f.minExp + 1) 0
  let ulp : Int := (if biased = 0 then f.minExp else exponent) - f.F
  let s : Int := ulp - exp
  if s ≤ 0 then (mant * 2 ^ (-s).toNat, if sticky then .low else .exact)
  else truncShift mant s.toNat sticky

/-- `FPRoundBase` after truncation: increment, carry, overflow and packing. -/
def aslTail (f : Fmt) (rm : RMode) (sign : Bool) (biased : Int) (intMant : Nat) (err : Err) :
    Bits f :=
  let (roundUp, overflowToInf) : Bool × Bool := aslRU rm sign intMant err
  let (intMant, biased) : Nat × Int :=
    if roundUp then
      let m := intMant + 1
      let b : Int := if m = 2 ^ f.F then 1 else biased
      if m = 2 ^ (f.F + 1) then (m / 2, b + 1) else (m, b)
    else (intMant, biased)
  if (f.expOnes : Int) ≤ biased then
    if overflowToInf then infinity f sign else maxNormal f sign
  else pack f sign biased.toNat (intMant % 2 ^ f.F)

theorem round_eq_tail (f : Fmt) (rm : RMode) (sign : Bool) (mant : Nat) (exp : Int) (st : Bool) :
    IEEE.round f rm sign mant exp st =
      if mant = 0 then zero f sign else
        aslTail f rm sign (Max.max ((mant.log2 : Int) + exp - f.minExp + 1) 0)
          (aslPair f mant exp st).1 (aslPair f mant exp st).2 := rfl

theorem truncShift_sticky (m k : Nat) (hk : 1 ≤ k) :
    truncShift m k true = truncShift (2 * m + 1) (k + 1) false := by
  have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hp1 : 2 ^ (k + 1) = 2 * 2 ^ k := Nat.pow_succ'
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod m (2 ^ k)
  have hq : (2 * m + 1) / 2 ^ (k + 1) = m / 2 ^ k := by
    rw [hp1, ← Nat.div_div_eq_div_mul]; congr 1; omega
  have hr2 : (2 * m + 1) % 2 ^ (k + 1) = 2 * (m % 2 ^ k) + 1 := by
    have : 2 * m + 1 = (2 * (m % 2 ^ k) + 1) + 2 ^ (k + 1) * (m / 2 ^ k) := by
      rw [hp1, Nat.mul_assoc]; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  unfold truncShift
  simp only [hq, hr2, Nat.add_sub_cancel, Prod.mk.injEq, true_and]
  generalize m % 2 ^ k = r at hr ⊢
  rw [hp] at hr ⊢
  generalize 2 ^ (k - 1) = H at hr hpos ⊢
  simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, and_false, ite_false,
    and_true, Nat.add_one_ne_zero]
  split_ifs <;> first | rfl | omega

theorem aslPair_sticky (f : Fmt) (m : Nat) (e : Int) (hm : 2 ^ (f.F + 1) ≤ m) :
    aslPair f m e true = aslPair f (2 * m + 1) (e - 1) false := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos (f.F + 1); omega
  have hL : f.F + 1 ≤ m.log2 := (Nat.le_log2 hm0).2 hm
  have hlog : (2 * m + 1).log2 = m.log2 + 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    have h1 := Nat.log2_self_le hm0
    have h2 := @Nat.lt_log2_self m
    rw [Nat.pow_succ] at h2 ⊢; rw [Nat.pow_succ]; constructor <;> omega
  unfold aslPair
  simp only [hlog]
  have hX : (((m.log2 + 1 : Nat)) : Int) + (e - 1) = (m.log2 : Int) + e := by push_cast; omega
  rw [hX]
  generalize hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = B
  have hs : 1 ≤ (if B = 0 then f.minExp else (m.log2 : Int) + e) - f.F - e := by
    split_ifs with h0
    · have : (m.log2 : Int) + e - f.minExp + 1 ≤ 0 := by rw [← h0] at *; omega
      omega
    · omega
  generalize (if B = 0 then f.minExp else (m.log2 : Int) + e) - f.F = U at hs ⊢
  rw [ite_eq_right (by omega), ite_eq_right (by omega),
    show (U - (e - 1)).toNat = (U - e).toNat + 1 by omega]
  exact truncShift_sticky m _ (by omega)

/-- Rounding `m / 2^k` to an integer in mode `rm` for a value of sign `s`. -/
def rq (rm : Mode) (s : Bool) (m k : Nat) : Nat :=
  match rm with
  | .nearestEven => FloatLib.Numerics.roundShiftRightEven m k
  | .towardZero => m >>> k
  | .towardPositiveInfinity => if s then m >>> k else Model.shiftRightCeilPow2 m k
  | .towardNegativeInfinity => if s then Model.shiftRightCeilPow2 m k else m >>> k

/-- Whether an overflowing magnitude of sign `s` is carried to the overflow value in mode `rm`. -/
def up (rm : Mode) (s : Bool) : Bool :=
  match rm with
  | .nearestEven => true
  | .towardZero => false
  | .towardPositiveInfinity => !s
  | .towardNegativeInfinity => s

/-- One rounder for all four modes, in the shape of FloatLib's `roundDyadicGeneral`. -/
def canon (fmt : FloatFormat) (rm : Mode) (s : Bool) (m : Nat) (e : Int) : Model fmt :=
  if m = 0 then Model.zero fmt s else
  if (m.log2 : Int) + e > fmt.maxNormalExponent then Model.directedOverflow fmt s (up rm s)
  else if (m.log2 : Int) + e < fmt.minNormalExponent then
    Model.packRoundedSubnormal fmt s (Model.zero fmt s)
      (match e - fmt.minSubnormalExponent with
       | .ofNat sh => m <<< sh
       | .negSucc sh => rq rm s m (sh + 1))
  else
    Model.packRoundedNormal fmt s (Model.directedOverflow fmt s (up rm s)) ((m.log2 : Int) + e)
      (if fmt.fracWidth ≤ m.log2 then rq rm s m (m.log2 - fmt.fracWidth)
       else m <<< (fmt.fracWidth - m.log2))

theorem ceil_eq (m k : Nat) :
    Model.shiftRightCeilPow2 m k = m / 2 ^ k + if m % 2 ^ k = 0 then 0 else 1 := by
  unfold Model.shiftRightCeilPow2
  by_cases hk : k = 0
  · subst hk; simp [Nat.mod_one]
  · have hdm := Nat.div_add_mod m (2 ^ k)
    have e1 : m.shiftRight k = m / 2 ^ k := Nat.shiftRight_eq_div_pow m k
    have e2 : ∀ a, a.shiftLeft k = a * 2 ^ k := fun a => Nat.shiftLeft_eq a k
    simp only [hk, beq_iff_eq, ite_false, e1, e2]
    have : m - m / 2 ^ k * 2 ^ k = m % 2 ^ k := by rw [Nat.mul_comm]; omega
    rw [this]; split_ifs <;> omega

theorem rq_zero (rm : Mode) (s : Bool) (m : Nat) : rq rm s m 0 = m := by
  cases rm <;> cases s <;>
    simp [rq, ceil_eq, FloatLib.Numerics.roundShiftRightEven_eq_roundQuotientEven,
      FloatLib.Numerics.roundQuotientEven, Nat.mod_one]

theorem rq_bounds (rm : Mode) (s : Bool) (m k : Nat) :
    m / 2 ^ k ≤ rq rm s m k ∧ rq rm s m k ≤ m / 2 ^ k + 1 := by
  cases rm <;> cases s <;>
    simp only [rq, ceil_eq, FloatLib.Numerics.roundShiftRightEven_eq_roundQuotientEven,
      FloatLib.Numerics.roundQuotientEven, Nat.shiftRight_eq_div_pow, Bool.false_eq_true,
      ite_true, ite_false] <;>
    first | omega | (split_ifs <;> omega)

theorem rne_eq_canon (fmt : FloatFormat) (s : Bool) (m : Nat) (e : Int) :
    Model.roundDyadicGeneral fmt ⟨s, m, e⟩ = canon fmt .nearestEven s m e := by
  simp only [Model.roundDyadicGeneral, canon, beq_iff_eq, rq, up, Model.directedOverflow,
    ite_true]
  split_ifs <;> rfl

/-- Leading-bit bounds. -/
theorem log2_bounds {m : Nat} (hm : m ≠ 0) : 2 ^ m.log2 ≤ m ∧ m < 2 * 2 ^ m.log2 := by
  have := @Nat.lt_log2_self m; rw [Nat.pow_succ] at this
  exact ⟨Nat.log2_self_le hm, by omega⟩

/-- The subnormal fraction fits the fraction field. -/
theorem sub_frac_lt (fmt : FloatFormat) (m : Nat) (e : Int) (hm : m ≠ 0)
    (hX : (m.log2 : Int) + e < fmt.minNormalExponent) :
    (match e - fmt.minSubnormalExponent with
      | .ofNat sh => m <<< sh
      | .negSucc sh => m >>> (sh + 1)) < 2 ^ fmt.fracWidth := by
  have hL := log2_bounds hm
  have hms : fmt.minSubnormalExponent = fmt.minNormalExponent - fmt.fracWidth := by
    simp [FloatFormat.minSubnormalExponent]
  split
  · rename_i sh hsh
    simp only [Int.ofNat_eq_natCast] at hsh
    rw [Nat.shiftLeft_eq]
    have : m.log2 + sh < fmt.fracWidth := by omega
    calc m * 2 ^ sh < 2 * 2 ^ m.log2 * 2 ^ sh := Nat.mul_lt_mul_of_pos_right hL.2 (Nat.two_pow_pos _)
      _ = 2 ^ (m.log2 + sh + 1) := by rw [Nat.pow_succ, Nat.pow_add]; ring
      _ ≤ 2 ^ fmt.fracWidth := Nat.pow_le_pow_right (by decide) (by omega)
  · rename_i sh hsh
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have : m.log2 < fmt.fracWidth + (sh + 1) := by
      have := Int.negSucc_eq sh; omega
    calc m < 2 * 2 ^ m.log2 := hL.2
      _ = 2 ^ (m.log2 + 1) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 ^ (fmt.fracWidth + (sh + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ fmt.fracWidth * 2 ^ (sh + 1) := Nat.pow_add _ _ _

theorem down_eq_canon (fmt : FloatFormat) (rm : Mode) (s : Bool) (m : Nat) (e : Int)
    (hm : m ≠ 0) (hrq : ∀ m k, rq rm s m k = m >>> k) (hup : up rm s = false) :
    Model.roundDyadicMagnitudeDown fmt s m e = canon fmt rm s m e := by
  have hL := log2_bounds hm
  have hF := fmt.fracWidth_pos
  have hms : fmt.minSubnormalExponent = fmt.minNormalExponent - fmt.fracWidth := by
    simp [FloatFormat.minSubnormalExponent]
  unfold Model.roundDyadicMagnitudeDown canon
  simp only [ite_eq_right hm, hrq, hup, Model.directedOverflow, Bool.false_eq_true, ite_false,
    Int.ofNat_eq_natCast]
  by_cases hA : (m.log2 : Int) + e > fmt.maxNormalExponent
  · simp only [ite_eq_left hA]
  simp only [ite_eq_right hA]
  by_cases hT : (m.log2 : Int) + e < fmt.minSubnormalExponent
  · rw [ite_eq_left hT, ite_eq_left (by omega)]
    obtain ⟨sh, hsh⟩ : ∃ sh, e - fmt.minSubnormalExponent = Int.negSucc sh :=
      ⟨(fmt.minSubnormalExponent - e - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
    have hsh' := Int.negSucc_eq sh
    have hz : m >>> (sh + 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]; apply Nat.div_eq_of_lt
      calc m < 2 * 2 ^ m.log2 := hL.2
        _ = 2 ^ (m.log2 + 1) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ (sh + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hsh, hz, Model.packRoundedSubnormal]; rfl
  rw [ite_eq_right hT]
  by_cases hS : (m.log2 : Int) + e < fmt.minNormalExponent
  · rw [ite_eq_left hS, ite_eq_left hS]
    have hlt := sub_frac_lt fmt m e hm hS
    generalize e - fmt.minSubnormalExponent = j at hlt ⊢
    have e1 : ∀ a b, Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq
    have e2 : ∀ a b, Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow
    cases j <;>
      simp only [Model.packRoundedSubnormal, Model.pow2_eq_two_pow, e1, e2, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow, beq_iff_eq] at hlt ⊢ <;>
      split_ifs <;> first | rfl | omega
  · rw [ite_eq_right hS, ite_eq_right hS]
    have hM : (if m.log2 ≥ fmt.fracWidth then Nat.shiftRight m (m.log2 - fmt.fracWidth)
        else Nat.shiftLeft m (fmt.fracWidth - m.log2)) < 2 ^ (fmt.fracWidth + 1) := by
      split_ifs with hc
      · show m >>> _ < _
        rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
          show fmt.fracWidth + 1 + (m.log2 - fmt.fracWidth) = m.log2 + 1 by omega, Nat.pow_succ]
        omega
      · show m <<< _ < _
        rw [Nat.shiftLeft_eq]
        calc m * 2 ^ (fmt.fracWidth - m.log2) < 2 * 2 ^ m.log2 * 2 ^ (fmt.fracWidth - m.log2) :=
              Nat.mul_lt_mul_of_pos_right hL.2 (Nat.two_pow_pos _)
          _ = 2 ^ (fmt.fracWidth + 1) := by
              rw [Nat.mul_assoc, ← Nat.pow_add, show m.log2 + (fmt.fracWidth - m.log2) =
                fmt.fracWidth by omega, Nat.pow_succ]; ring
    have e1 : ∀ a b, Nat.shiftLeft a b = a <<< b := fun _ _ => rfl
    have e2 : ∀ a b, Nat.shiftRight a b = a >>> b := fun _ _ => rfl
    simp only [e1, e2, ge_iff_le] at hM ⊢
    generalize (if fmt.fracWidth ≤ m.log2 then m >>> (m.log2 - fmt.fracWidth)
        else m <<< (fmt.fracWidth - m.log2)) = M at hM ⊢
    simp only [Model.packRoundedNormal, Model.pow2_eq_two_pow, beq_iff_eq,
      show M ≠ 2 ^ (fmt.fracWidth + 1) by omega, ite_false, ite_eq_right hA, Int.ofNat_eq_natCast]

theorem up_eq_canon (fmt : FloatFormat) (rm : Mode) (s : Bool) (m : Nat) (e : Int)
    (hm : m ≠ 0) (hrq : ∀ m k, rq rm s m k = Model.shiftRightCeilPow2 m k)
    (hup : up rm s = true) :
    Model.roundDyadicMagnitudeUp fmt s m e = canon fmt rm s m e := by
  have hL := log2_bounds hm
  have hF := fmt.fracWidth_pos
  have hms : fmt.minSubnormalExponent = fmt.minNormalExponent - fmt.fracWidth := by
    simp [FloatFormat.minSubnormalExponent]
  unfold Model.roundDyadicMagnitudeUp canon
  simp only [ite_eq_right hm, hrq, hup, Model.directedOverflow, ite_true, Int.ofNat_eq_natCast]
  by_cases hA : (m.log2 : Int) + e > fmt.maxNormalExponent
  · simp only [ite_eq_left hA]
  simp only [ite_eq_right hA]
  have hF2 : 2 ≤ 2 ^ fmt.fracWidth := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ fmt.fracWidth := Nat.pow_le_pow_right (by decide) hF
  by_cases hT : (m.log2 : Int) + e < fmt.minSubnormalExponent
  · rw [ite_eq_left hT, ite_eq_left (by omega)]
    obtain ⟨sh, hsh⟩ : ∃ sh, e - fmt.minSubnormalExponent = Int.negSucc sh :=
      ⟨(fmt.minSubnormalExponent - e - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
    have hsh' := Int.negSucc_eq sh
    have hlt : m < 2 ^ (sh + 1) :=
      calc m < 2 * 2 ^ m.log2 := hL.2
        _ = 2 ^ (m.log2 + 1) := by rw [Nat.pow_succ]; ring
        _ ≤ 2 ^ (sh + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : Model.shiftRightCeilPow2 m (sh + 1) = 1 := by
      rw [ceil_eq, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, ite_eq_right hm]
    simp only [hsh, h1, Model.packRoundedSubnormal, Model.pow2_eq_two_pow]
    simp only [show ¬ (1 = 0) by omega, show ¬ (1 ≥ 2 ^ fmt.fracWidth) by omega, beq_iff_eq,
      ite_false]
  rw [ite_eq_right hT]
  by_cases hS : (m.log2 : Int) + e < fmt.minNormalExponent
  · rw [ite_eq_left hS, ite_eq_left hS]
    generalize e - fmt.minSubnormalExponent = j
    have hpos : 0 < m := Nat.pos_of_ne_zero hm
    have e1 : ∀ a b, Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq
    cases j
    · rename_i sh
      have : m * 2 ^ sh ≠ 0 := Nat.mul_ne_zero hm (by positivity)
      simp only [Model.packRoundedSubnormal, e1, Nat.shiftLeft_eq, beq_iff_eq, this, ite_false]
    · rename_i sh
      have : Model.shiftRightCeilPow2 m (sh + 1) ≠ 0 := by
        rw [ceil_eq]; intro h0
        have h1 : m / 2 ^ (sh + 1) = 0 := (Nat.add_eq_zero_iff.mp h0).1
        have h2 : m % 2 ^ (sh + 1) = 0 := by
          by_contra hc; rw [ite_eq_right hc] at h0; exact absurd h0 (Nat.succ_ne_zero _)
        have := Nat.div_add_mod m (2 ^ (sh + 1)); rw [h1, h2] at this; omega
      simp only [Model.packRoundedSubnormal, beq_iff_eq, this, ite_false]
  · rw [ite_eq_right hS, ite_eq_right hS]
    rfl

theorem roundDyadicWithRounding_eq_canon (fmt : FloatFormat) (rm : Mode) (s : Bool) (m : Nat)
    (e : Int) : Model.roundDyadicWithRounding fmt rm ⟨s, m, e⟩ = canon fmt rm s m e := by
  cases rm
  · show Model.roundDyadic fmt ⟨s, m, e⟩ = _
    rw [← Model.roundDyadicGeneral_eq_roundDyadic, rne_eq_canon]
  all_goals by_cases hm : m = 0
  all_goals try (subst hm; simp [Model.roundDyadicWithRounding, Model.roundDyadicTowardZero,
    Model.roundDyadicUp, Model.roundDyadicDown, canon])
  · simp only [Model.roundDyadicWithRounding, Model.roundDyadicTowardZero, beq_iff_eq, ite_eq_right hm]
    exact down_eq_canon fmt _ s m e hm (fun _ _ => rfl) rfl
  · simp only [Model.roundDyadicWithRounding, Model.roundDyadicUp, beq_iff_eq, ite_eq_right hm]
    cases s
    · exact up_eq_canon fmt _ false m e hm (fun _ _ => rfl) rfl
    · exact down_eq_canon fmt _ true m e hm (fun _ _ => rfl) rfl
  · simp only [Model.roundDyadicWithRounding, Model.roundDyadicDown, beq_iff_eq, ite_eq_right hm]
    cases s
    · exact down_eq_canon fmt _ false m e hm (fun _ _ => rfl) rfl
    · exact up_eq_canon fmt _ true m e hm (fun _ _ => rfl) rfl

theorem maxNormalExponent_fl : (fl f h).maxNormalExponent = (f.bias : Int) := by
  rw [FloatFormat.maxNormalExponent_eq_ieee _ (fl_isIEEE h)]; rfl

theorem minNormalExponent_fl : (fl f h).minNormalExponent = f.minExp := rfl

theorem minSubnormalExponent_fl : (fl f h).minSubnormalExponent = f.minExp - f.F := rfl

theorem maxFiniteExpField_fl : (fl f h).maxFiniteExpField = f.expOnes - 1 := by
  simp only [FloatFormat.maxFiniteExpField, fl_encoding, fl_expWidth,
    FloatFormat.Encoding.maxFiniteExponent, Fmt.expOnes]; omega

theorem maxFiniteFracField_fl : (fl f h).maxFiniteFracField = 2 ^ f.F - 1 := rfl

theorem expOnes_eq (h : FmtOk f) : f.expOnes = 2 * f.bias + 1 := by
  have := two_pow_E h; simp only [Fmt.expOnes]; omega

theorem aslRU_snd (rm : Mode) (s : Bool) (q : Nat) (err : Err) :
    (aslRU rm.asl s q err).2 = up rm s := by
  cases rm <;> rfl

theorem aslRU_exact (rm : Mode) (s : Bool) (q : Nat) :
    (aslRU rm.asl s q .exact).1 = false := by
  cases rm <;> cases s <;> simp [aslRU, Model.IEEERoundingMode.asl]

theorem rq_asl (rm : Mode) (s : Bool) (m k : Nat) (hk : 1 ≤ k) :
    rq rm s m k =
      if (aslRU rm.asl s (truncShift m k false).1 (truncShift m k false).2).1 then
        (truncShift m k false).1 + 1
      else (truncShift m k false).1 := by
  have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpos : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  cases rm <;> cases s <;>
    simp only [rq, aslRU, truncShift, Model.IEEERoundingMode.asl, ceil_eq,
      FloatLib.Numerics.roundShiftRightEven_eq_roundQuotientEven,
      FloatLib.Numerics.roundQuotientEven, Nat.shiftRight_eq_div_pow, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, and_true, and_false, ite_true, ite_false] <;>
    generalize m % 2 ^ k = r at hr ⊢ <;>
    generalize m / 2 ^ k = q <;>
    simp only [hp] at hr ⊢ <;>
    generalize 2 ^ (k - 1) = H at hr hpos ⊢ <;>
    split_ifs <;> simp_all <;> omega

theorem ofM_directedOverflow (s u : Bool) :
    ofM f h (Model.directedOverflow (fl f h) s u) = if u then infinity f s else maxNormal f s := by
  cases u <;> simp only [Model.directedOverflow, ite_true, ite_false, Bool.false_eq_true,
    ofM_nativeOverflow, ofM_maxFinite]

theorem tail_normal (rm : RMode) (s : Bool) (B : Int) (q : Nat) (err : Err)
    (hq1 : 2 ^ f.F ≤ q) (hq2 : q < 2 ^ (f.F + 1)) :
    aslTail f rm s B q err =
      if (if (aslRU rm s q err).1 then q + 1 else q) = 2 ^ (f.F + 1) then
        (if (f.expOnes : Int) ≤ B + 1 then
          (if (aslRU rm s q err).2 then infinity f s else maxNormal f s)
         else pack f s (B + 1).toNat 0)
      else if (f.expOnes : Int) ≤ B then
        (if (aslRU rm s q err).2 then infinity f s else maxNormal f s)
      else pack f s B.toNat ((if (aslRU rm s q err).1 then q + 1 else q) - 2 ^ f.F) := by
  have hp : 2 ^ (f.F + 1) = 2 * 2 ^ f.F := Nat.pow_succ'
  unfold aslTail
  generalize aslRU rm s q err = p
  obtain ⟨ru, oi⟩ := p
  cases ru
  · simp only [Bool.false_eq_true, ite_false, show q ≠ 2 ^ (f.F + 1) by omega]
    rw [Nat.mod_eq_sub_mod hq1, Nat.mod_eq_of_lt (by omega)]
  · simp only [show q + 1 ≠ 2 ^ f.F by omega, ↓reduceIte]
    by_cases hc : q + 1 = 2 ^ (f.F + 1)
    · simp only [hc, ↓reduceIte, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2),
        Nat.mod_self]
    · simp only [hc, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem tail_sub (rm : RMode) (s : Bool) (q : Nat) (err : Err) (hq : q < 2 ^ f.F)
    (h3 : 3 ≤ f.expOnes) :
    aslTail f rm s 0 q err =
      if (if (aslRU rm s q err).1 then q + 1 else q) = 2 ^ f.F then pack f s 1 0
      else pack f s 0 (if (aslRU rm s q err).1 then q + 1 else q) := by
  have hp : 2 ^ (f.F + 1) = 2 * 2 ^ f.F := Nat.pow_succ'
  unfold aslTail
  generalize aslRU rm s q err = p
  obtain ⟨ru, oi⟩ := p
  cases ru
  · simp only [Bool.false_eq_true, ite_false, show q ≠ 2 ^ f.F by omega,
      show ¬ ((f.expOnes : Int) ≤ 0) by omega, Nat.mod_eq_of_lt hq]; rfl
  · simp only [show q + 1 ≠ 2 ^ (f.F + 1) by omega, ↓reduceIte]
    by_cases hc : q + 1 = 2 ^ f.F
    · simp only [hc, ↓reduceIte, Nat.mod_self, show ¬ ((f.expOnes : Int) ≤ 1) by omega]; rfl
    · simp only [hc, ↓reduceIte, Nat.mod_eq_of_lt (show q + 1 < 2 ^ f.F by omega),
        show ¬ ((f.expOnes : Int) ≤ 0) by omega]; rfl

theorem finish_normal (s : Bool) (X : Int) (hX : f.minExp ≤ X) (M : Nat) (hM1 : 2 ^ f.F ≤ M)
    (hM2 : M ≤ 2 ^ (f.F + 1)) (u : Bool) :
    (if M = 2 ^ (f.F + 1) then
        (if (f.expOnes : Int) ≤ X + f.bias + 1 then
          (if u then infinity f s else maxNormal f s)
         else pack f s (X + f.bias + 1).toNat 0)
      else if (f.expOnes : Int) ≤ X + f.bias then
        (if u then infinity f s else maxNormal f s)
      else pack f s (X + f.bias).toNat (M - 2 ^ f.F)) =
    ofM f h (if X > (f.bias : Int) then Model.directedOverflow (fl f h) s u
      else Model.packRoundedNormal (fl f h) s (Model.directedOverflow (fl f h) s u) X M) := by
  have hE := two_pow_E h
  have hO := expOnes_eq h
  have hp : 2 ^ (f.F + 1) = 2 * 2 ^ f.F := Nat.pow_succ'
  have hmin : f.minExp = 1 - (f.bias : Int) := rfl
  rw [hO]
  simp only [Model.packRoundedNormal, Model.pow2_eq_two_pow, beq_iff_eq, maxNormalExponent_fl,
    fl_exponentBias, fl_fracWidth, maxFiniteExpField_fl, maxFiniteFracField_fl, hO,
    Int.ofNat_eq_natCast]
  by_cases hc : M = 2 ^ (f.F + 1)
  · simp only [hc, ite_true, Nat.sub_self]
    by_cases hov : X > (f.bias : Int)
    · rw [ite_eq_left (by push_cast; omega), ite_eq_left hov, ofM_directedOverflow]
    · rw [ite_eq_right hov]
      by_cases hov1 : X + 1 > (f.bias : Int)
      · rw [ite_eq_left (by push_cast; omega), ite_eq_left hov1, ofM_directedOverflow]
      · rw [ite_eq_right (by push_cast; omega), ite_eq_right hov1]
        have hlt : (X + 1 + f.bias).toNat ≤ 2 * f.bias := by omega
        simp only [show ¬ ((X + 1 + f.bias).toNat > 2 * f.bias + 1 - 1) by omega,
          decide_false, Bool.false_or, Bool.and_false, Bool.false_eq_true,
          ite_false, gt_iff_lt, Nat.not_lt_zero]
        rw [ofM_ofFields h _ _ _ (by omega) (Nat.two_pow_pos _)]
        congr 1; omega
  · simp only [hc, ite_false]
    by_cases hov : X > (f.bias : Int)
    · rw [ite_eq_left (by push_cast; omega), ite_eq_left hov, ofM_directedOverflow]
    · rw [ite_eq_right (by push_cast; omega), ite_eq_right hov, ite_eq_right hov]
      have hlt : (X + f.bias).toNat ≤ 2 * f.bias := by omega
      simp only [show ¬ ((X + f.bias).toNat > 2 * f.bias + 1 - 1) by omega,
        show ¬ (M - 2 ^ f.F > 2 ^ f.F - 1) by omega, decide_false, Bool.false_or,
        Bool.and_false, Bool.false_eq_true, ite_false]
      rw [ofM_ofFields h _ _ _ (by omega) (by omega)]

theorem finish_sub (s : Bool) (M : Nat) (hM : M ≤ 2 ^ f.F) :
    (if M = 2 ^ f.F then pack f s 1 0 else pack f s 0 M) =
      ofM f h (Model.packRoundedSubnormal (fl f h) s (Model.zero (fl f h) s) M) := by
  have hE : 2 ≤ 2 ^ f.E := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f.E := Nat.pow_le_pow_right (by decide) (by have := h.E2; omega)
  have hF := Nat.two_pow_pos f.F
  simp only [Model.packRoundedSubnormal, Model.pow2_eq_two_pow, beq_iff_eq, fl_fracWidth]
  by_cases h0 : M = 0
  · simp only [h0, ite_true, show (0 : Nat) ≠ 2 ^ f.F by omega, ite_false, ofM_zero]; rfl
  · rw [ite_eq_right h0]
    by_cases hc : M = 2 ^ f.F
    · simp only [hc, ite_true, ge_iff_le, le_refl]
      rw [ofM_ofFields h _ _ _ (by omega) hF]
    · rw [ite_eq_right hc, ite_eq_right (by omega), ofM_ofFields h _ _ _ (Nat.two_pow_pos _) (by omega)]

theorem aslPair_normal (m : Nat) (e : Int) (hX : f.minExp ≤ (m.log2 : Int) + e) :
    aslPair f m e false =
      if m.log2 ≤ f.F then (m * 2 ^ (f.F - m.log2), .exact)
      else truncShift m (m.log2 - f.F) false := by
  have hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = (m.log2 : Int) + e - f.minExp + 1 :=
    max_eq_left (by omega)
  unfold aslPair
  simp only
  rw [hB, ite_eq_right (show ¬ ((m.log2 : Int) + e - f.minExp + 1 = 0) by omega),
    show (m.log2 : Int) + e - f.F - e = (m.log2 : Int) - f.F by omega]
  by_cases hLF : m.log2 ≤ f.F
  · rw [ite_eq_left (by omega : (m.log2 : Int) - f.F ≤ 0), ite_eq_left hLF,
      show (-((m.log2 : Int) - f.F)).toNat = f.F - m.log2 by omega]
    rfl
  · rw [ite_eq_right (by omega : ¬ ((m.log2 : Int) - f.F ≤ 0)), ite_eq_right hLF,
      show ((m.log2 : Int) - f.F).toNat = m.log2 - f.F by omega]

theorem aslPair_sub_ofNat (m : Nat) (e : Int) (hX : (m.log2 : Int) + e < f.minExp) (sh : Nat)
    (hsh : e - (f.minExp - f.F) = Int.ofNat sh) :
    aslPair f m e false = (m * 2 ^ sh, .exact) := by
  have hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = 0 := max_eq_right (by omega)
  simp only [Int.ofNat_eq_natCast] at hsh
  unfold aslPair
  simp only
  rw [hB, ite_eq_left rfl, show f.minExp - f.F - e = -(sh : Int) by omega,
    ite_eq_left (by omega : -(sh : Int) ≤ 0), show (-(-(sh : Int))).toNat = sh by omega]
  rfl

theorem aslPair_sub_negSucc (m : Nat) (e : Int) (hX : (m.log2 : Int) + e < f.minExp) (sh : Nat)
    (hsh : e - (f.minExp - f.F) = Int.negSucc sh) :
    aslPair f m e false = truncShift m (sh + 1) false := by
  have := Int.negSucc_eq sh
  have hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = 0 := max_eq_right (by omega)
  unfold aslPair
  simp only
  rw [hB, ite_eq_left rfl, show f.minExp - f.F - e = (sh : Int) + 1 by omega,
    ite_eq_right (by omega : ¬ ((sh : Int) + 1 ≤ 0)), show ((sh : Int) + 1).toNat = sh + 1 by omega]

theorem round_eq_canon (rm : Mode) (s : Bool) (m : Nat) (e : Int) :
    IEEE.round f rm.asl s m e = ofM f h (canon (fl f h) rm s m e) := by
  rw [round_eq_tail]
  by_cases hm : m = 0
  · subst hm; rw [ite_eq_left rfl]; unfold canon; rw [ite_eq_left rfl, ofM_zero]
  have hL := log2_bounds hm
  have hE := two_pow_E h
  have h3 := expOnes_pos h
  have hF := h.F1
  have hmin : f.minExp = 1 - (f.bias : Int) := rfl
  rw [ite_eq_right hm]
  unfold canon
  rw [ite_eq_right hm]
  rw [maxNormalExponent_fl, minNormalExponent_fl, minSubnormalExponent_fl, fl_fracWidth]
  by_cases hS : (m.log2 : Int) + e < f.minExp
  · rw [ite_eq_right (by omega), ite_eq_left hS]
    have hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = 0 := max_eq_right (by omega)
    rw [hB]
    cases hj : e - (f.minExp - f.F) with
    | ofNat sh =>
      rw [aslPair_sub_ofNat m e hS sh hj]
      simp only [Int.ofNat_eq_natCast] at hj
      have hlt : m * 2 ^ sh < 2 ^ f.F :=
        calc m * 2 ^ sh < 2 * 2 ^ m.log2 * 2 ^ sh :=
              Nat.mul_lt_mul_of_pos_right hL.2 (Nat.two_pow_pos _)
          _ = 2 ^ (m.log2 + sh + 1) := by rw [Nat.pow_succ, Nat.pow_add]; ring
          _ ≤ 2 ^ f.F := Nat.pow_le_pow_right (by decide) (by omega)
      rw [tail_sub _ _ _ _ hlt h3, aslRU_exact]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [finish_sub h s _ hlt.le]
      congr 2
      show m * 2 ^ sh = m <<< sh
      rw [Nat.shiftLeft_eq]
    | negSucc sh =>
      rw [aslPair_sub_negSucc m e hS sh hj]
      have := Int.negSucc_eq sh
      have hlt : (truncShift m (sh + 1) false).1 < 2 ^ f.F := by
        show m / 2 ^ (sh + 1) < _
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        calc m < 2 * 2 ^ m.log2 := hL.2
          _ = 2 ^ (m.log2 + 1) := by rw [Nat.pow_succ]; ring
          _ ≤ 2 ^ (f.F + (sh + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 2 ^ f.F * 2 ^ (sh + 1) := Nat.pow_add _ _ _
      have hb := rq_bounds rm s m (sh + 1)
      have hts : (truncShift m (sh + 1) false).1 = m / 2 ^ (sh + 1) := rfl
      have hra := rq_asl rm s m (sh + 1) (by omega)
      rw [tail_sub _ _ _ _ hlt h3, ← hra]
      exact finish_sub h s _ (by omega)
  · rw [ite_eq_right hS]
    have hB : Max.max ((m.log2 : Int) + e - f.minExp + 1) 0 = (m.log2 : Int) + e + f.bias := by
      rw [max_eq_left (by omega)]; omega
    rw [hB, aslPair_normal m e (by omega)]
    by_cases hLF : m.log2 ≤ f.F
    · rw [ite_eq_left hLF]
      have hq1 : 2 ^ f.F ≤ m * 2 ^ (f.F - m.log2) :=
        calc 2 ^ f.F = 2 ^ m.log2 * 2 ^ (f.F - m.log2) := by
              rw [← Nat.pow_add]; congr 1; omega
          _ ≤ m * 2 ^ (f.F - m.log2) := Nat.mul_le_mul_right _ hL.1
      have hq2 : m * 2 ^ (f.F - m.log2) < 2 ^ (f.F + 1) :=
        calc m * 2 ^ (f.F - m.log2) < 2 * 2 ^ m.log2 * 2 ^ (f.F - m.log2) :=
              Nat.mul_lt_mul_of_pos_right hL.2 (Nat.two_pow_pos _)
          _ = 2 ^ (f.F + 1) := by
              rw [Nat.mul_assoc, ← Nat.pow_add, show m.log2 + (f.F - m.log2) = f.F by omega,
                Nat.pow_succ]; ring
      rw [tail_normal _ _ _ _ _ hq1 hq2, aslRU_exact, aslRU_snd]
      simp only [Bool.false_eq_true, ite_false]
      have hM : (if f.F ≤ m.log2 then rq rm s m (m.log2 - f.F) else m <<< (f.F - m.log2)) =
          m * 2 ^ (f.F - m.log2) := by
        split_ifs with hc
        · rw [show m.log2 - f.F = 0 by omega, rq_zero, show f.F - m.log2 = 0 by omega]; simp
        · rw [Nat.shiftLeft_eq]
      rw [hM]
      have := finish_normal h s ((m.log2 : Int) + e) (by omega) _ hq1 hq2.le (up rm s)
      simp only [show m * 2 ^ (f.F - m.log2) ≠ 2 ^ (f.F + 1) by omega, ite_false] at this ⊢
      exact this
    · rw [ite_eq_right hLF]
      have hk : 1 ≤ m.log2 - f.F := by omega
      have hq1 : 2 ^ f.F ≤ (truncShift m (m.log2 - f.F) false).1 := by
        show _ ≤ m / 2 ^ (m.log2 - f.F)
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add,
          show f.F + (m.log2 - f.F) = m.log2 by omega]
        exact hL.1
      have hq2 : (truncShift m (m.log2 - f.F) false).1 < 2 ^ (f.F + 1) := by
        show m / 2 ^ (m.log2 - f.F) < _
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
          show f.F + 1 + (m.log2 - f.F) = m.log2 + 1 by omega, Nat.pow_succ]
        omega
      rw [tail_normal _ _ _ _ _ hq1 hq2, aslRU_snd, ← rq_asl rm s m _ hk,
        ite_eq_left (by omega : f.F ≤ m.log2)]
      have hb := rq_bounds rm s m (m.log2 - f.F)
      have hts : (truncShift m (m.log2 - f.F) false).1 = m / 2 ^ (m.log2 - f.F) := rfl
      exact finish_normal h s ((m.log2 : Int) + e) (by omega) _ (by omega) (by omega) (up rm s)

end BasicAux

open BasicAux

/-- `FPRound` of the exact value `(-1)^s * m * 2^e` (no sticky tail) is FloatLib's rounding of
that dyadic, in every `FPCR` rounding mode, including zero, subnormal, carry and overflow
results. -/
theorem round_eq (rm : Mode) (s : Bool) (m : Nat) (e : Int) :
    round f rm.asl s m e = ofM f h (Model.roundDyadicWithRounding (fl f h) rm ⟨s, m, e⟩) := by
  rw [round_eq_canon h, roundDyadicWithRounding_eq_canon]

/-- A sticky tail below the rounding position (`m ≥ 2^(F+1)`) rounds like one appended `1` bit:
`FPRound` of `(m + δ) * 2^e`, `0 < δ < 1`, is that of the exact `(2m + 1) * 2^(e-1)`. -/
theorem round_sticky (rm : RMode) (s : Bool) (m : Nat) (e : Int) (hm : 2 ^ (f.F + 1) ≤ m) :
    round f rm s m e true = round f rm s (2 * m + 1) (e - 1) := by
  have hm0 : m ≠ 0 := by have := Nat.two_pow_pos (f.F + 1); omega
  have hlog : (2 * m + 1).log2 = m.log2 + 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    have h1 := Nat.log2_self_le hm0
    have h2 := @Nat.lt_log2_self m
    rw [Nat.pow_succ] at h2 ⊢; rw [Nat.pow_succ]; constructor <;> omega
  rw [round_eq_tail, round_eq_tail, ite_eq_right hm0, ite_eq_right (by omega), aslPair_sticky f m e hm, hlog]
  congr 2; push_cast; omega

end IEEE.Spec

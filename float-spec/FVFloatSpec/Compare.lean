import FVFloatSpec.Basic
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder

/-!
# `FPMax`, `FPMin`, `FPCompare`, `FPNeg`, `FPAbs` against FloatLib

`max_eq`/`min_eq`: the Arm max/min (NaNs via `FPProcessNaNs`, the selected operand re-rounded
by `FPRound`, which returns it unchanged in every mode) are FloatLib's `maximum`/`minimum`.
`compare_eq`: `FPCompare`'s value order (`cmpVal`) is FloatLib's `compare`.
`neg_eq`/`abs_eq`: sign-bit operations. Generic in the format, with `_b32`/`_b64` corollaries.
-/

namespace IEEE.Spec

open FloatLib.Floats.Formats.BinaryInterchange

private theorem cmpDyadic_eq_addExact (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat)
    (e2 : Int) :
    Model.cmpDyadic ⟨s1, m1, e1⟩ ⟨s2, m2, e2⟩ =
      (if (addExact s1 m1 e1 (!s2) m2 e2).1 < 0 then .lt
       else if (addExact s1 m1 e1 (!s2) m2 e2).1 = 0 then .eq else .gt) := by
  rw [Model.cmpDyadic_eq_cmpDyadicAligned]
  simp only [Model.cmpDyadicAligned, addExact, signed]
  have hmin : Min.min e1 e2 = (if e1 ≤ e2 then e1 else e2) := by
    split <;> omega
  simp only [hmin, show ∀ m k : Nat, Nat.shiftLeft m k = m * 2 ^ k from fun m k => Nat.shiftLeft_eq m k,
    Int.ofNat_eq_natCast]
  generalize (if e1 ≤ e2 then e1 else e2) = e
  have hk1 : 0 < 2 ^ (e1 - e).toNat := by positivity
  have hk2 : 0 < 2 ^ (e2 - e).toNat := by positivity
  generalize 2 ^ (e1 - e).toNat = k1 at *
  generalize 2 ^ (e2 - e).toNat = k2 at *
  have h1 : m1 = 0 ↔ m1 * k1 = 0 := by simp [Nat.pos_iff_ne_zero.1 hk1]
  have h2 : m2 = 0 ↔ m2 * k2 = 0 := by simp [Nat.pos_iff_ne_zero.1 hk2]
  generalize m1 * k1 = a at *
  generalize m2 * k2 = b at *
  cases s1 <;> cases s2 <;> simp only [Bool.not_true, Bool.not_false] <;>
    split_ifs <;> simp_all <;>
    first
    | (rw [compare_lt_iff_lt]; omega)
    | (rw [compare_gt_iff_gt]; omega)
    | omega

private theorem pack_self (f : Fmt) (x : Bits f) : pack f (signOf f x) (expOf f x) (fracOf f x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [pack, signOf, expOf, fracOf, BitVec.toNat_ofNat]
  have hx := x.isLt
  set n := x.toNat
  have hm : n % (2 ^ f.F * 2 ^ f.E) = n % 2 ^ f.F + 2 ^ f.F * (n / 2 ^ f.F % 2 ^ f.E) :=
    Nat.mod_mul
  rw [← Nat.pow_add, Nat.add_comm f.F] at hm
  have hd := Nat.div_add_mod n (2 ^ (f.E + f.F))
  have hlt : n / 2 ^ (f.E + f.F) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have : 2 ^ (1 + f.E + f.F) = 2 * 2 ^ (f.E + f.F) := by
      rw [Nat.add_assoc, Nat.pow_add, Nat.pow_one]
    omega
  have hpos : 0 < 2 ^ (f.E + f.F) := by positivity
  have hn : BitVec.toNat x = n := rfl
  simp only [hn]
  by_cases hc : 2 ^ (f.E + f.F) ≤ n
  · have : n / 2 ^ (f.E + f.F) = 1 := 
      Nat.le_antisymm (by omega) ((Nat.le_div_iff_mul_le hpos).2 (by omega))
    rw [this] at hd; rw [Nat.mul_comm] at hm
    simp only [hc, decide_true, ite_true]
    rw [Nat.mod_eq_of_lt] <;> omega
  · have : n / 2 ^ (f.E + f.F) = 0 := by
      rw [Nat.div_eq_zero_iff]; omega
    rw [this] at hd; rw [Nat.mul_comm] at hm
    simp only [hc, decide_false, Bool.false_eq_true, ite_false]
    rw [Nat.mod_eq_of_lt] <;> omega

private theorem round_normal (f : Fmt) (rm : RMode) (s : Bool) (b fr : Nat) (hb1 : 1 ≤ b)
    (hb2 : b < f.expOnes) (hfr : fr < 2 ^ f.F) :
    IEEE.round f rm s (2 ^ f.F + fr) ((b : Int) - f.bias - f.F) = pack f s b fr := by
  have hm : 2 ^ f.F + fr ≠ 0 := by positivity
  have hlog : (2 ^ f.F + fr).log2 = f.F := by
    apply Nat.le_antisymm
    · have := (Nat.log2_lt hm).2 (show 2 ^ f.F + fr < 2 ^ (f.F + 1) by rw [Nat.pow_succ]; omega)
      omega
    · exact (Nat.le_log2 hm).2 (by omega)
  unfold IEEE.round
  have h1 : Max.max ((f.F : Int) + ((b : Int) - f.bias - f.F) - (1 - f.bias) + 1) 0 = b := by
    omega
  have h2 : ((f.F : Int) + ((b : Int) - f.bias - f.F)) - f.F - ((b : Int) - f.bias - f.F) = 0 := by
    omega
  have h3 : ¬ ((f.expOnes : Int) ≤ b) := by omega
  have h4 : (2 ^ f.F + fr) % 2 ^ f.F = fr := by simp [Nat.mod_eq_of_lt hfr]
  simp only [hm, ite_false, hlog, Fmt.minExp, h1, show ((b : Int) = 0) = False by simp; omega,
    h2, le_refl, ite_true, Int.neg_zero, Int.toNat_zero, pow_zero, mul_one]
  cases rm <;> simp [h3, h4]

private theorem round_denormal (f : Fmt) (rm : RMode) (s : Bool) (fr : Nat) (hE : 1 ≤ f.expOnes)
    (hfr0 : fr ≠ 0) (hfr : fr < 2 ^ f.F) :
    IEEE.round f rm s fr (f.minExp - f.F) = pack f s 0 fr := by
  have hlog : fr.log2 < f.F := (Nat.log2_lt hfr0).2 hfr
  unfold IEEE.round
  generalize fr.log2 = L at hlog
  have h1 : Max.max ((L : Int) + (f.minExp - f.F) - f.minExp + 1) 0 = 0 := by omega
  have h2 : (f.minExp - f.F) - (f.minExp - f.F) = (0 : Int) := by omega
  simp only [hfr0, ite_false, h1, ite_true, h2, le_refl, Int.neg_zero, Int.toNat_zero, pow_zero,
    mul_one]
  cases rm <;> simp [Nat.mod_eq_of_lt hfr] <;> omega

private theorem expOnes_ge (f : Fmt) (h : FmtOk f) : 3 ≤ f.expOnes := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h.E2
  simp only [Fmt.expOnes]; omega

/-- The non-NaN branch of `FPMax`/`FPMin` returns the selected operand unchanged. -/
private theorem sel_self (f : Fmt) (h : FmtOk f) (rm : RMode) (x : Bits f) (s' : Bool)
    (hnan : (typeOf f x).isNaN = false) (hz : typeOf f x = .zero → s' = signOf f x) :
    (if (unpack f x).1 = .infinity then infinity f (unpack f x).2.1
      else if (unpack f x).1 = .zero then zero f s'
      else IEEE.round f rm (unpack f x).2.1 (unpack f x).2.2.1 (unpack f x).2.2.2) = x := by
  have hE := expOnes_ge f h
  have hfr : fracOf f x < 2 ^ f.F := Nat.mod_lt _ (by positivity)
  have hb : expOf f x < 2 ^ f.E := Nat.mod_lt _ (by positivity)
  conv_rhs => rw [← pack_self f x]
  unfold typeOf at hnan hz
  unfold unpack at hnan hz ⊢
  generalize signOf f x = sg at *
  generalize expOf f x = b at *
  generalize fracOf f x = fr at *
  by_cases hb0 : b = 0
  · subst hb0
    by_cases hf0 : fr = 0
    · subst hf0
      simp only [ite_true, reduceCtorEq, ite_false, true_implies] at hz ⊢
      rw [hz]; rfl
    · simp only [ite_true, hf0, ite_false, reduceCtorEq]
      exact round_denormal f rm sg fr (by omega) hf0 hfr
  · by_cases hb1 : b = f.expOnes
    · by_cases hf0 : fr = 0
      · have hEne : f.expOnes ≠ 0 := by omega
        subst hf0 hb1; simp [hEne, infinity]
      · have hEne : f.expOnes ≠ 0 := by omega
        subst hb1
        simp only [hEne, hf0, ite_false, ite_true] at hnan
        split_ifs at hnan <;> simp [FPType.isNaN] at hnan
    · simp only [hb0, hb1, ite_false, reduceCtorEq]
      exact round_normal f rm sg b fr (by omega) (by simp only [Fmt.expOnes] at hb1 ⊢; omega) hfr

private theorem unpack_sign (f : Fmt) (x : Bits f) : (unpack f x).2.1 = signOf f x := by
  unfold unpack; dsimp only; split_ifs <;> rfl

private theorem isNaN_toM_false (f : Fmt) (h : FmtOk f) {x : Bits f} (hx : (typeOf f x).isNaN = false) :
    Model.isNaN (toM f h x) = false := by
  rw [isNaN_toM]; exact hx

/-- The Arm value comparison of two non-NaN operands is FloatLib's `compareNonNaN`. -/
private theorem cmpVal_eq (f : Fmt) (h : FmtOk f) (a b : Bits f) (ha : (typeOf f a).isNaN = false)
    (hb : (typeOf f b).isNaN = false) :
    cmpVal (unpack f a).1 (unpack f a).2.1 (unpack f a).2.2.1 (unpack f a).2.2.2
        (unpack f b).1 (unpack f b).2.1 (unpack f b).2.2.1 (unpack f b).2.2.2 =
      Model.compareNonNaN (toM f h a) (toM f h b) (isNaN_toM_false f h ha)
        (isNaN_toM_false f h hb) := by
  have hta : (unpack f a).1 = typeOf f a := rfl
  have htb : (unpack f b).1 = typeOf f b := rfl
  unfold Model.compareNonNaN cmpVal
  simp only [hta, htb, unpack_sign]
  by_cases hia : typeOf f a = .infinity <;> by_cases hib : typeOf f b = .infinity
  · simp [hia, hib, isInf_toM, signBit_toM]
  · simp [hia, beq_eq_false_iff_ne.mpr hib, hib, isInf_toM, signBit_toM]
  · simp [hib, beq_eq_false_iff_ne.mpr hia, hia, isInf_toM, signBit_toM]
  · have hda := toDyadic?_toM h a
    have hdb := toDyadic?_toM h b
    simp only [ha, hb, hia, hib, Bool.false_eq_true, or_self, ite_false] at hda hdb
    simp [beq_eq_false_iff_ne.mpr hia, beq_eq_false_iff_ne.mpr hib, hia, hib, isInf_toM,
      Model.finiteDyadic_eq_of_toDyadic _ hda,
      Model.finiteDyadic_eq_of_toDyadic _ hdb, cmpDyadic_eq_addExact, unpack_sign]

theorem compare_eq (f : Fmt) (h : FmtOk f) (a b : Bits f) :
    IEEE.compare f a b =
      match Model.compare (toM f h a) (toM f h b) with
      | some .lt => .lt
      | some .eq => .eq
      | some .gt => .gt
      | none => .un := by
  by_cases ha : (typeOf f a).isNaN = true
  · have : Model.compare (toM f h a) (toM f h b) = none :=
      by
      unfold Model.compare
      rw [dite_eq_left_of_eq_true (eq_true (by simp [isNaN_toM, ha]))]
    rw [this]; simp [IEEE.compare, typeOf] at ha ⊢; simp [ha]
  by_cases hb : (typeOf f b).isNaN = true
  · have : Model.compare (toM f h a) (toM f h b) = none :=
      by
      unfold Model.compare
      rw [dite_eq_left_of_eq_true (eq_true (by simp [isNaN_toM, hb]))]
    rw [this]; simp [IEEE.compare, typeOf] at hb ⊢; simp [hb]
  simp only [Bool.not_eq_true] at ha hb
  have hc := cmpVal_eq f h a b ha hb
  have : Model.compare (toM f h a) (toM f h b) =
      some (Model.compareNonNaN (toM f h a) (toM f h b) (isNaN_toM_false f h ha)
        (isNaN_toM_false f h hb)) := by
    unfold Model.compare
    rw [dite_eq_right_of_eq_false (eq_false (by simp [isNaN_toM_false f h ha, isNaN_toM_false f h hb]))]
  rw [this, ← hc]
  simp only [typeOf] at ha hb
  simp only [IEEE.compare, ha, hb, Bool.false_eq_true, or_self, ite_false]
  generalize cmpVal _ _ _ _ _ _ _ _ = c
  cases c <;> rfl

private theorem getLsbD_sign (f : Fmt) (a : Bits f) : a.getLsbD (f.E + f.F) = signOf f a := by
  have h1 := BitVec.msb_eq_decide a
  have h2 := BitVec.msb_eq_getLsbD_last a
  have hk : 1 + f.E + f.F - 1 = f.E + f.F := by omega
  rw [hk] at h1 h2
  rw [← h2, h1]; rfl

private theorem abs_bits (f : Fmt) (a : Bits f) : IEEE.abs f a = if signOf f a then neg f a else a := by
  have hs := getLsbD_sign f a
  unfold IEEE.abs neg
  split <;> rename_i hc <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow] <;>
    rcases Nat.lt_trichotomy i (f.E + f.F) with hlt | heq | hgt
  all_goals first
    | omega
    | (subst heq; rw [BitVec.getLsbD_eq_getElem hi] at hs; simp_all)
    | simp [hlt, hi, show f.E + f.F ≠ i by omega]

theorem neg_eq (f : Fmt) (h : FmtOk f) (a : Bits f) :
    IEEE.neg f a = ofM f h (Model.neg (toM f h a)) := (ofM_neg h a).symm

theorem abs_eq (f : Fmt) (h : FmtOk f) (a : Bits f) :
    IEEE.abs f a = ofM f h (Model.abs (toM f h a)) := by
  have hz : (fl f h).supportsSignedZero = true := rfl
  have hp : Model.signBit (Model.posZero (fl f h)) = false := by
    simp [Model.signBit, Model.posZero, Model.ofNatBits, Model.ofBits, FloatFormat.ofWordNat]
  rw [abs_bits, ← ofM_neg h a]
  unfold Model.abs Model.copySign Model.neg
  simp only [hz, hp, signBit_toM h, Bool.not_true, Bool.false_and, ite_true]
  cases signOf f a <;> simp

private theorem cmpVal_gt_left_zero (t1 : FPType) (s1 : Bool) (e1 : Int) (t2 : FPType) (s2 : Bool)
    (m2 : Nat) (e2 : Int) (ht : t1 ≠ .infinity) (hc : cmpVal t1 s1 0 e1 t2 s2 m2 e2 = .gt) :
    s2 = true := by
  have ht' : (t1 == .infinity) = false := beq_eq_false_iff_ne.mpr ht
  unfold cmpVal at hc
  rw [ht'] at hc
  cases hb : t2 == .infinity <;> rw [hb] at hc <;> cases s1 <;> cases s2 <;>
    simp only [addExact, signed, Bool.not_true, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, reduceCtorEq, Nat.zero_mul, Int.natCast_zero, Int.neg_zero,
      Int.zero_add] at hc <;> (try split_ifs at hc) <;>
    first | rfl | omega

private theorem cmpVal_lt_left_zero (t1 : FPType) (s1 : Bool) (e1 : Int) (t2 : FPType) (s2 : Bool)
    (m2 : Nat) (e2 : Int) (ht : t1 ≠ .infinity) (hc : cmpVal t1 s1 0 e1 t2 s2 m2 e2 = .lt) :
    s2 = false := by
  have ht' : (t1 == .infinity) = false := beq_eq_false_iff_ne.mpr ht
  unfold cmpVal at hc
  rw [ht'] at hc
  cases hb : t2 == .infinity <;> rw [hb] at hc <;> cases s1 <;> cases s2 <;>
    simp only [addExact, signed, Bool.not_true, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, reduceCtorEq, Nat.zero_mul, Int.natCast_zero, Int.neg_zero,
      Int.zero_add] at hc <;> (try split_ifs at hc) <;>
    first | rfl | omega

private theorem cmpVal_lt_right_zero (t1 : FPType) (s1 : Bool) (m1 : Nat) (e1 : Int) (t2 : FPType)
    (s2 : Bool) (e2 : Int) (ht : t2 ≠ .infinity) (hc : cmpVal t1 s1 m1 e1 t2 s2 0 e2 = .lt) :
    s1 = true := by
  have ht' : (t2 == .infinity) = false := beq_eq_false_iff_ne.mpr ht
  unfold cmpVal at hc
  rw [ht'] at hc
  cases hb : t1 == .infinity <;> rw [hb] at hc <;> cases s1 <;> cases s2 <;>
    simp only [addExact, signed, Bool.not_true, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, reduceCtorEq, Nat.zero_mul, Int.natCast_zero, Int.neg_zero,
      ] at hc <;> (try split_ifs at hc) <;>
    first | rfl | omega

private theorem cmpVal_gt_right_zero (t1 : FPType) (s1 : Bool) (m1 : Nat) (e1 : Int) (t2 : FPType)
    (s2 : Bool) (e2 : Int) (ht : t2 ≠ .infinity) (hc : cmpVal t1 s1 m1 e1 t2 s2 0 e2 = .gt) :
    s1 = false := by
  have ht' : (t2 == .infinity) = false := beq_eq_false_iff_ne.mpr ht
  unfold cmpVal at hc
  rw [ht'] at hc
  cases hb : t1 == .infinity <;> rw [hb] at hc <;> cases s1 <;> cases s2 <;>
    simp only [addExact, signed, Bool.not_true, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, reduceCtorEq, Nat.zero_mul, Int.natCast_zero, Int.neg_zero,
      ] at hc <;> (try split_ifs at hc) <;>
    first | rfl | omega

private theorem mant_zero_iff (f : Fmt) (x : Bits f) (hnan : (typeOf f x).isNaN = false)
    (hinf : typeOf f x ≠ .infinity) : (unpack f x).2.2.1 = 0 ↔ typeOf f x = .zero := by
  unfold typeOf at hnan hinf ⊢
  unfold unpack at hnan hinf ⊢
  dsimp only at hnan hinf ⊢
  split_ifs at hnan hinf ⊢ <;> simp_all [FPType.isNaN]

private theorem mant_zero (f : Fmt) (x : Bits f) (hz : typeOf f x = .zero) : (unpack f x).2.2.1 = 0 :=
  (mant_zero_iff f x (by rw [hz]; rfl) (by rw [hz]; decide)).2 hz

private theorem inf_fields (f : Fmt) (x : Bits f) (hx : typeOf f x = .infinity) :
    pack f (signOf f x) f.expOnes 0 = x := by
  conv_rhs => rw [← pack_self f x]
  unfold typeOf unpack at hx
  dsimp only at hx
  split_ifs at hx with h1 h2 h3 h4
  simp_all

/-- Two non-NaN operands that compare equal and are not both zeros are the same encoding. -/
private theorem eq_of_cmpVal_eq (f : Fmt) (h : FmtOk f) (a b : Bits f)
    (ha : (typeOf f a).isNaN = false) (hb : (typeOf f b).isNaN = false)
    (hc : cmpVal (unpack f a).1 (unpack f a).2.1 (unpack f a).2.2.1 (unpack f a).2.2.2
        (unpack f b).1 (unpack f b).2.1 (unpack f b).2.2.1 (unpack f b).2.2.2 = .eq)
    (hz : ¬ (typeOf f a = .zero ∧ typeOf f b = .zero)) : a = b := by
  have hta : (unpack f a).1 = typeOf f a := rfl
  have htb : (unpack f b).1 = typeOf f b := rfl
  by_cases hia : typeOf f a = .infinity <;> by_cases hib : typeOf f b = .infinity
  · simp only [cmpVal, hta, htb, hia, hib, unpack_sign, beq_self_eq_true] at hc
    split_ifs at hc with hs
    rw [← inf_fields f a hia, ← inf_fields f b hib, hs]
  · simp [cmpVal, hta, htb, hia, beq_eq_false_iff_ne.mpr hib] at hc
    split_ifs at hc
  · simp [cmpVal, hta, htb, hib, beq_eq_false_iff_ne.mpr hia] at hc
    split_ifs at hc
  · have hda := toDyadic?_toM h a
    have hdb := toDyadic?_toM h b
    simp only [ha, hb, hia, hib, Bool.false_eq_true, or_self, ite_false] at hda hdb
    simp only [cmpVal, hta, htb, beq_eq_false_iff_ne.mpr hia, beq_eq_false_iff_ne.mpr hib,
      unpack_sign] at hc
    have hd : Model.cmpDyadic ⟨signOf f a, (unpack f a).2.2.1, (unpack f a).2.2.2⟩
        ⟨signOf f b, (unpack f b).2.2.1, (unpack f b).2.2.2⟩ = .eq := by
      rw [cmpDyadic_eq_addExact]; exact hc
    rw [Model.cmpDyadic_eq_iff] at hd
    rw [unpack_sign] at hda hdb
    have hfa := Model.isFinite_eq_true_of_toDyadic?_some hda
    have hfb := Model.isFinite_eq_true_of_toDyadic?_some hdb
    have hva : Model.toReal (toM f h a) = FloatLib.Numerics.Dyadic.toReal
        ⟨signOf f a, (unpack f a).2.2.1, (unpack f a).2.2.2⟩ := by simp [Model.toReal_eq, hda]
    have hvb : Model.toReal (toM f h b) = FloatLib.Numerics.Dyadic.toReal
        ⟨signOf f b, (unpack f b).2.2.1, (unpack f b).2.2.2⟩ := by simp [Model.toReal_eq, hdb]
    have hne : Model.toReal (toM f h a) ≠ 0 := by
      intro h0
      rw [hva] at h0
      have h0' := h0
      rw [hd] at h0'
      rw [Model.Dyadic.toReal_eq_zero_iff] at h0 h0'
      exact hz ⟨(mant_zero_iff f a ha hia).1 h0, (mant_zero_iff f b hb hib).1 h0'⟩
    have := Model.eq_of_toReal_eq_of_nonzero hfa hfb (by rw [hva, hvb, hd]) hne
    simpa using congrArg (ofM f h) this

private theorem maximum_of_some {fmt : FloatFormat} (x y r : Model fmt)
    (hn : Model.chooseNaN2 x y = some r) : Model.maximum x y = r := by
  unfold Model.maximum Model.withNaNSelection
  rw [dite_eq_right_of_eq_false (eq_false (by simp [hn]))]; simp [hn]

private theorem minimum_of_some {fmt : FloatFormat} (x y r : Model fmt)
    (hn : Model.chooseNaN2 x y = some r) : Model.minimum x y = r := by
  unfold Model.minimum Model.withNaNSelection
  rw [dite_eq_right_of_eq_false (eq_false (by simp [hn]))]; simp [hn]

private theorem maximum_of_none {fmt : FloatFormat} (x y : Model fmt)
    (hn : Model.chooseNaN2 x y = none) (hx : Model.isNaN x = false)
    (hy : Model.isNaN y = false) :
    Model.maximum x y =
      match Model.compareNonNaN x y hx hy with
      | .lt => y
      | .gt => x
      | .eq => if Model.isZero x && Model.isZero y then
          Model.zero fmt (Model.signBit x && Model.signBit y) else x := by
  unfold Model.maximum Model.withNaNSelection
  rw [dite_eq_left_of_eq_true (eq_true hn)]; rfl

private theorem minimum_of_none {fmt : FloatFormat} (x y : Model fmt)
    (hn : Model.chooseNaN2 x y = none) (hx : Model.isNaN x = false)
    (hy : Model.isNaN y = false) :
    Model.minimum x y =
      match Model.compareNonNaN x y hx hy with
      | .lt => x
      | .gt => y
      | .eq => if Model.isZero x && Model.isZero y then
          Model.zero fmt (Model.signBit x || Model.signBit y) else x := by
  unfold Model.minimum Model.withNaNSelection
  rw [dite_eq_left_of_eq_true (eq_true hn)]; rfl

/-- NaN operands: both sides return `FPProcessNaNs`' choice; otherwise the operands are not NaNs
and FloatLib selects no NaN. -/
private theorem nan_split (f : Fmt) (h : FmtOk f) (a b : Bits f) :
    (∃ r, processNaNs f (typeOf f a) (typeOf f b) a b = some (ofM f h r) ∧
        Model.chooseNaN2 (toM f h a) (toM f h b) = some r) ∨
      (processNaNs f (typeOf f a) (typeOf f b) a b = none ∧
        Model.chooseNaN2 (toM f h a) (toM f h b) = none ∧
        (typeOf f a).isNaN = false ∧ (typeOf f b).isNaN = false) := by
  have hN := chooseNaN2_toM h a b
  cases hc : Model.chooseNaN2 (toM f h a) (toM f h b) with
  | some r => exact Or.inl ⟨r, by rw [← hN, hc]; rfl, rfl⟩
  | none =>
    right
    rw [hc] at hN
    have := (Model.chooseNaN2_eq_none_iff _ _).1 hc
    rw [isNaN_toM, isNaN_toM] at this
    exact ⟨hN.symm, rfl, this⟩

theorem max_eq (f : Fmt) (h : FmtOk f) (rm : RMode) (a b : Bits f) :
    IEEE.max f rm a b = ofM f h (Model.maximum (toM f h a) (toM f h b)) := by
  rcases nan_split f h a b with ⟨r, hp, hc⟩ | ⟨hp, hc, ha, hb⟩
  · rw [maximum_of_some _ _ _ hc]
    unfold IEEE.max
    simp only []
    rw [show processNaNs f (unpack f a).1 (unpack f b).1 a b = some (ofM f h r) from hp]
  rw [maximum_of_none _ _ hc (isNaN_toM_false f h ha) (isNaN_toM_false f h hb),
    ← cmpVal_eq f h a b ha hb]
  unfold IEEE.max
  simp only []
  rw [show processNaNs f (unpack f a).1 (unpack f b).1 a b = none from hp]
  simp only []
  have hta : (unpack f a).1 = typeOf f a := rfl
  have htb : (unpack f b).1 = typeOf f b := rfl
  cases hcv : cmpVal (unpack f a).1 (unpack f a).2.1 (unpack f a).2.2.1 (unpack f a).2.2.2
      (unpack f b).1 (unpack f b).2.1 (unpack f b).2.2.1 (unpack f b).2.2.2 with
  | gt =>
    simp only [↓reduceIte, ofM_toM]
    refine sel_self f h rm a _ ha (fun hz => ?_)
    rw [mant_zero f a hz] at hcv
    have := cmpVal_gt_left_zero _ _ _ _ _ _ _ (by rw [hta, hz]; decide) hcv
    rw [unpack_sign, unpack_sign] at *; simp [this]
  | lt =>
    simp only [reduceCtorEq, ↓reduceIte, ofM_toM]
    refine sel_self f h rm b _ hb (fun hz => ?_)
    rw [mant_zero f b hz] at hcv
    have := cmpVal_lt_right_zero _ _ _ _ _ _ _ (by rw [htb, hz]; decide) hcv
    rw [unpack_sign, unpack_sign] at *; simp [this]
  | eq =>
    simp only [reduceCtorEq, ↓reduceIte]
    by_cases hz : typeOf f a = .zero ∧ typeOf f b = .zero
    · have hza : Model.isZero (toM f h a) = true := by rw [isZero_toM]; simp [hz.1]
      have hzb : Model.isZero (toM f h b) = true := by rw [isZero_toM]; simp [hz.2]
      simp only [hza, hzb, Bool.and_self, ↓reduceIte, ofM_zero, signBit_toM, htb, hz.2,
        reduceCtorEq, unpack_sign]
    · have hab := eq_of_cmpVal_eq f h a b ha hb hcv hz
      have hza : (Model.isZero (toM f h a) && Model.isZero (toM f h b)) = false := by
        rw [isZero_toM, isZero_toM, ← hab]; simp only [Bool.and_self, decide_eq_false_iff_not]
        rw [← hab] at hz; exact fun h' => hz ⟨h', h'⟩
      simp only [hza, Bool.false_eq_true, ↓reduceIte, ofM_toM]
      subst hab
      exact sel_self f h rm a _ ha (fun hz' => absurd ⟨hz', hz'⟩ hz)

theorem min_eq (f : Fmt) (h : FmtOk f) (rm : RMode) (a b : Bits f) :
    IEEE.min f rm a b = ofM f h (Model.minimum (toM f h a) (toM f h b)) := by
  rcases nan_split f h a b with ⟨r, hp, hc⟩ | ⟨hp, hc, ha, hb⟩
  · rw [minimum_of_some _ _ _ hc]
    unfold IEEE.min
    simp only []
    rw [show processNaNs f (unpack f a).1 (unpack f b).1 a b = some (ofM f h r) from hp]
  rw [minimum_of_none _ _ hc (isNaN_toM_false f h ha) (isNaN_toM_false f h hb),
    ← cmpVal_eq f h a b ha hb]
  unfold IEEE.min
  simp only []
  rw [show processNaNs f (unpack f a).1 (unpack f b).1 a b = none from hp]
  simp only []
  have hta : (unpack f a).1 = typeOf f a := rfl
  have htb : (unpack f b).1 = typeOf f b := rfl
  cases hcv : cmpVal (unpack f a).1 (unpack f a).2.1 (unpack f a).2.2.1 (unpack f a).2.2.2
      (unpack f b).1 (unpack f b).2.1 (unpack f b).2.2.1 (unpack f b).2.2.2 with
  | lt =>
    simp only [↓reduceIte, ofM_toM]
    refine sel_self f h rm a _ ha (fun hz => ?_)
    rw [mant_zero f a hz] at hcv
    have := cmpVal_lt_left_zero _ _ _ _ _ _ _ (by rw [hta, hz]; decide) hcv
    rw [unpack_sign, unpack_sign] at *; simp [this]
  | gt =>
    simp only [reduceCtorEq, ↓reduceIte, ofM_toM]
    refine sel_self f h rm b _ hb (fun hz => ?_)
    rw [mant_zero f b hz] at hcv
    have := cmpVal_gt_right_zero _ _ _ _ _ _ _ (by rw [htb, hz]; decide) hcv
    rw [unpack_sign, unpack_sign] at *; simp [this]
  | eq =>
    simp only [reduceCtorEq, ↓reduceIte]
    by_cases hz : typeOf f a = .zero ∧ typeOf f b = .zero
    · have hza : Model.isZero (toM f h a) = true := by rw [isZero_toM]; simp [hz.1]
      have hzb : Model.isZero (toM f h b) = true := by rw [isZero_toM]; simp [hz.2]
      simp only [hza, hzb, Bool.and_self, ↓reduceIte, ofM_zero, signBit_toM, htb, hz.2,
        reduceCtorEq, unpack_sign]
    · have hab := eq_of_cmpVal_eq f h a b ha hb hcv hz
      have hza : (Model.isZero (toM f h a) && Model.isZero (toM f h b)) = false := by
        rw [isZero_toM, isZero_toM, ← hab]; simp only [Bool.and_self, decide_eq_false_iff_not]
        rw [← hab] at hz; exact fun h' => hz ⟨h', h'⟩
      simp only [hza, Bool.false_eq_true, ↓reduceIte, ofM_toM]
      subst hab
      exact sel_self f h rm a _ ha (fun hz' => absurd ⟨hz', hz'⟩ hz)

end IEEE.Spec

namespace IEEE.Spec
open FloatLib.Floats.Formats.BinaryInterchange

theorem max_eq_b32 (rm : RMode) (a b : Bits .b32) :
    IEEE.max .b32 rm a b = ofM .b32 FmtOk.b32 (Model.maximum (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  max_eq _ _ rm a b
theorem max_eq_b64 (rm : RMode) (a b : Bits .b64) :
    IEEE.max .b64 rm a b = ofM .b64 FmtOk.b64 (Model.maximum (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  max_eq _ _ rm a b
theorem min_eq_b32 (rm : RMode) (a b : Bits .b32) :
    IEEE.min .b32 rm a b = ofM .b32 FmtOk.b32 (Model.minimum (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b)) :=
  min_eq _ _ rm a b
theorem min_eq_b64 (rm : RMode) (a b : Bits .b64) :
    IEEE.min .b64 rm a b = ofM .b64 FmtOk.b64 (Model.minimum (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b)) :=
  min_eq _ _ rm a b
theorem compare_eq_b32 (a b : Bits .b32) :
    IEEE.compare .b32 a b =
      match Model.compare (toM .b32 FmtOk.b32 a) (toM .b32 FmtOk.b32 b) with
      | some .lt => .lt | some .eq => .eq | some .gt => .gt | none => .un :=
  compare_eq _ _ a b
theorem compare_eq_b64 (a b : Bits .b64) :
    IEEE.compare .b64 a b =
      match Model.compare (toM .b64 FmtOk.b64 a) (toM .b64 FmtOk.b64 b) with
      | some .lt => .lt | some .eq => .eq | some .gt => .gt | none => .un :=
  compare_eq _ _ a b
theorem neg_eq_b32 (a : Bits .b32) :
    IEEE.neg .b32 a = ofM .b32 FmtOk.b32 (Model.neg (toM .b32 FmtOk.b32 a)) := neg_eq _ _ a
theorem neg_eq_b64 (a : Bits .b64) :
    IEEE.neg .b64 a = ofM .b64 FmtOk.b64 (Model.neg (toM .b64 FmtOk.b64 a)) := neg_eq _ _ a
theorem abs_eq_b32 (a : Bits .b32) :
    IEEE.abs .b32 a = ofM .b32 FmtOk.b32 (Model.abs (toM .b32 FmtOk.b32 a)) := abs_eq _ _ a
theorem abs_eq_b64 (a : Bits .b64) :
    IEEE.abs .b64 a = ofM .b64 FmtOk.b64 (Model.abs (toM .b64 FmtOk.b64 a)) := abs_eq _ _ a

end IEEE.Spec

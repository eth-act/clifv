import FV.Opt.Proof.MidValNormFam5

/-!
# Family 6 is a sound normaliser under typing (#1119 stage 2, agent MidendNext5)

Shapes around shifts and masks in the `rewrite:operand` tail (#1119 issuecomment-7200665739),
after Cranelift 0.135.0's `opts/shifts.isle` and `opts/cprop.isle`, each proved against
`Clif.evalInst`:

* `fam6Mul` — `imul ty a 2^s` (`0 < s < width`) and `iadd ty a a` are `a << s` (`mulShAmt_val`);
  with `a` a shift of `y` by a constant `K`, `(y << K) << s` is `y << (K mod w + s)` below the
  width (`BitVec.shiftLeft_add`), `(y >> s) << s` is `y & (-1 << s)` for `ushr`
  (`BitVec.shiftLeft_ushiftRight`) and `sshr` (`sshiftRight_shiftLeft`); no typing: both sides
  read `y` at type `ty`;
* `shAmt` (typed) — a shift or rotation reads its amount modulo the width, which divides `2^8`
  (`width_dvd_256`), so an amount given as an `uextend`, `sextend` or `ireduce` (all keep the low 8
  bits, `low8_*`) of a term `y` shifts as `y` (`shiftAmt_of_low8`); the extension or truncation
  has a value exactly when `y` has one of a narrower (wider) type, hence the typing;
* `reStep` — `op (op x k1) k2` is `op x (k1 op k2)` for `band`, `bor`, `bxor`, `imul`
  (associativity), and `imul (x << k) c` is `imul x (c << k)` (`shiftLeft_eq_mul_twoPow`); no
  typing.

The neutral constant the narrowing of `ireduce` leaves (`narrowId`) is proved with the
narrowing, `ruleSoundT_narrowStep` (`FV/Opt/Proof/MidValNormFam4.lean`). None of these rules drops
an operand.

Main results: `ruleSound_fam6Mul`, `ruleSoundT_shAmt`, `ruleSound_reStep`, `ruleSoundT_fam6Step`,
and, moved here from `MidValNormFam5.lean` with their statements unchanged (`Norm.base` now
starts with `fam6Mul` and ends with family 6): `normSoundT_base`, `normSoundT_narrowN` and
**`normSoundT_stdT : NormSoundT f (Norm.stdT f)`** (the validator's default normaliser).
-/

namespace Opt.MidVal

open Clif

/-! ## Widths -/

theorem width_dvd_256 (ty : Ty) : ty.width ∣ 256 := by cases ty <;> decide

theorem width_ge_8 (ty : Ty) : 8 ≤ ty.width := by cases ty <;> decide

theorem width_le_128 (ty : Ty) : ty.width ≤ 128 := by cases ty <;> decide

/-- A width of at least 8 bits keeps the low 8 bits: `2^8` divides `2^w`. -/
theorem dvd_two_pow_of_ge_8 {w : Nat} (h : 8 ≤ w) : 256 ∣ 2 ^ w := by
  have := Nat.pow_dvd_pow 2 h
  simpa using this

/-! ## Shift amounts -/

/-- Shift amounts with the same low 8 bits shift alike (the amount counts modulo the width). -/
theorem shiftAmt_of_low8 {v1 v2 : Nat} (ty : Ty) {y1 : BitVec v1} {y2 : BitVec v2}
    (h : y1.toNat % 256 = y2.toNat % 256) : Sem.shiftAmt ty.width y1 = Sem.shiftAmt ty.width y2 := by
  unfold Sem.shiftAmt
  rw [← Nat.mod_mod_of_dvd y1.toNat (width_dvd_256 ty), h,
    Nat.mod_mod_of_dvd y2.toNat (width_dvd_256 ty)]

theorem low8_setWidth {w v : Nat} (y : BitVec w) (hv : 8 ≤ v) :
    (y.setWidth v).toNat % 256 = y.toNat % 256 := by
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (dvd_two_pow_of_ge_8 hv)]

theorem low8_signExtend {w v : Nat} (y : BitVec w) (hw : 8 ≤ w) (hv : 8 ≤ v) :
    (y.signExtend v).toNat % 256 = y.toNat % 256 := by
  have e : (y.signExtend v).setWidth 8 = y.setWidth 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
    have h1 : i < v := by omega
    have h2 : i < w := by omega
    simp [hi, h1, h2]
  have := congrArg BitVec.toNat e
  simpa [BitVec.toNat_setWidth] using this

/-- A shift or rotation by amounts that shift alike. -/
theorem shift_congr {w v1 v2 : Nat} (op : BinaryOp) (x : BitVec w) {y1 : BitVec v1}
    {y2 : BitVec v2} (h : Sem.shiftAmt w y1 = Sem.shiftAmt w y2) :
    Sem.shift op x y1 = Sem.shift op x y2 := by
  cases op <;> simp [Sem.shift, Sem.ishl, Sem.ushr, Sem.sshr, Sem.rotl, Sem.rotr, h]

/-- A shift or rotation: `x` read at the node's type, the amount any value. -/
theorem evalNode_shift {F : Frame} {mem : Mem} {op : BinaryOp} {ty : Ty} {x y : ValueId}
    (hop : op.isShift = true) :
    evalNode F mem (.binary op ty x y) =
      ((F.regs x).bind (·.as? ty)).bind fun A => (F.regs y).bind fun B =>
        (Sem.shift op A B.bits).map fun r => ⟨ty, r⟩ := by
  simp only [evalNode, evalInst, Frame.getAs, Frame.get, hop, ite_true]
  rcases ha : F.regs x with _ | va
  · simp [Res.ofOption, bind, Res.bind]
  · cases hA : va.as? ty with
    | none => simp [Res.ofOption, Res.bind, bind, hA]
    | some A =>
      rcases hb : F.regs y with _ | vb
      · simp [Res.ofOption, Res.bind, bind, pure, hA]
      · cases hs : Sem.shift op A vb.bits <;> simp [Res.ofOption, Res.bind, bind, pure, hA, hs]

theorem shift_isSome {w v : Nat} {op : BinaryOp} (hop : op.isShift = true) (x : BitVec w)
    (y : BitVec v) : ∃ r, Sem.shift op x y = some r := by
  cases op <;> simp_all [BinaryOp.isShift, Sem.shift]

/-! ## `shAmt` -/

theorem ruleSoundT_shAmt {f : Function} : RuleSoundT f (shAmt (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  cases i with
  | binary op ty x b =>
    simp only [shAmt] at h
    split at h
    · rename_i hop
      -- the amount `b` and the term `y` it is made of, with `y`'s value typed
      have key : ∀ (y : Nat) (j : Inst), nodeAt tms b = some j → y ∈ operands j →
          x' = .node (.binary op ty x y) →
          (∀ v, (tmFrame f tms fr mem).regs y = some v →
            ∃ B, evalNode (tmFrame f tms fr mem) mem j = some B ∧
              B.bits.toNat % 256 = v.bits.toNat % 256) →
          ((tmFrame f tms fr mem).regs y = none → evalNode (tmFrame f tms fr mem) mem j = none) →
          tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty x b) := by
        intro y j hj _ hx hsome hnone
        subst hx
        have hna := nodeAt_spec hj
        have hbv : (tmFrame f tms fr mem).regs b = evalNode (tmFrame f tms fr mem) mem j :=
          tmVal_node hna.1 hna.2
        rw [tmVal_res ht hord, evalNode_shift hop, evalNode_shift hop, hbv]
        rcases hv : (tmFrame f tms fr mem).regs y with _ | v
        · rw [hnone hv]
        · obtain ⟨B, hB, hlow⟩ := hsome v hv
          rw [hB]
          rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty) with _ | A
          · rfl
          · simp only [Option.bind_some]
            rw [shift_congr op A (shiftAmt_of_low8 ty hlow)]
      split at h
      · rename_i eop ety y hb
        split at h
        · rename_i yt hyt
          split at h
          · rename_i hw
            cases h
            have hna := nodeAt_spec hb
            have hry : TmReach tms (.binary op ty x b) y :=
              .sub (.op (by simp [operands])) hna.1 (by simp [operands])
            refine key y _ hb (by simp [operands]) rfl ?_ ?_
            · intro v hv
              have hvt : v.ty = yt := tyAt_val hA hry hyt hv
              refine ⟨⟨ety, extOp eop ety.width v.bits⟩, ?_, ?_⟩
              · rw [evalNode_extend, hv]
                simp [hvt, hw]
              · cases eop
                · simp only [extOp, Sem.uextend]
                  rw [BitVec.zeroExtend_eq_setWidth, low8_setWidth _ (width_ge_8 ety)]
                · simp only [extOp, Sem.sextend]
                  exact low8_signExtend _ (width_ge_8 _) (width_ge_8 ety)
            · intro hv
              rw [evalNode_extend, hv]
              rfl
          · cases h
        · cases h
      · rename_i rty y hb
        split at h
        · rename_i yt hyt
          split at h
          · rename_i hw
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
            cases h
            have hna := nodeAt_spec hb
            have hry : TmReach tms (.binary op ty x b) y :=
              .sub (.op (by simp [operands])) hna.1 (by simp [operands])
            refine key y _ hb (by simp [operands]) rfl ?_ ?_
            · intro v hv
              have hvt : v.ty = yt := tyAt_val hA hry hyt hv
              refine ⟨⟨rty, BitVec.setWidth rty.width v.bits⟩, ?_, low8_setWidth _ (width_ge_8 rty)⟩
              rw [evalNode_ireduce, hv]
              simp [hvt, hw.1]
            · intro hv
              rw [evalNode_ireduce, hv]
              rfl
          · cases h
        · cases h
      · cases h
    · cases h
  | _ => simp [shAmt] at h

/-! ## `fam6Mul` -/

/-- `a << s` as a multiplication: `a * 2^s` and `a + a` (`s = 1`). -/
theorem mulShAmt_val {tms : Array Tm} {ty : Ty} {op : BinaryOp} {a b a' s : Nat}
    (h : mulShAmt tms ty op a b = some (a', s)) :
    a' = a ∧ s < ty.width ∧ op.isShift = false ∧
      ∀ (f : Function) (fr : Frame) (mem : Mem),
        evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) =
          (((tmFrame f tms fr mem).regs a).bind (·.as? ty)).map fun A => ⟨ty, A <<< s⟩ := by
  unfold mulShAmt at h
  split at h
  · split at h
    · rename_i k hk
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨hp, -⟩, hs⟩ := hc
        generalize hd : k.toNat.log2 = d at hp hs h
        cases h
        refine ⟨rfl, hs, rfl, fun f fr mem => ?_⟩
        have hkv : (tmFrame f tms fr mem).regs b = some ⟨ty, k⟩ := constAt_spec hk
        rw [evalNode_binary_nonShift rfl, hkv]
        have hkt : k = BitVec.twoPow ty.width s := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hs)]
          exact hp.symm
        rcases ((tmFrame f tms fr mem).regs a).bind (·.as? ty) with _ | A
        · rfl
        · simp [Sem.binary, Sem.imul, hkt]
      · cases h
    · cases h
  · split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      cases h
      refine ⟨rfl, Nat.lt_of_lt_of_le (by decide) (width_ge_8 ty), rfl, fun f fr mem => ?_⟩
      rw [evalNode_binary_nonShift rfl]
      rcases ((tmFrame f tms fr mem).regs a).bind (·.as? ty) with _ | A
      · rfl
      · simp only [Option.bind_some, Option.map_some, Sem.binary, Sem.iadd]
        congr 2
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
        congr 1
        omega
    · cases h
  · cases h

/-- `(y >>ₛ s) << s` clears the low `s` bits. -/
theorem sshiftRight_shiftLeft {w : Nat} (y : BitVec w) (s : Nat) :
    y.sshiftRight s <<< s = y &&& BitVec.allOnes w <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_sshiftRight, hi, decide_true, Bool.true_and]
  by_cases h1 : i < s
  · simp [h1]
  · have h2 : i - s + s = i := by omega
    have h3 : i - s < w := by omega
    have h4 : ¬ w ≤ i - s := by omega
    have h5 : s + (i - s) = i := by omega
    simp [h1, h2, h3, h4, h5, hi]

/-- The node `shlPlan` gives for `a` and `s < width` has the value of `a << s`. -/
theorem shlPlan_val {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {ty : Ty}
    {a s y kc : Nat} {op' : BinaryOp} {K : Val} (h : shlPlan tms ty a s = some (op', y, K))
    (hs : s < ty.width) (hK : (tmFrame f tms fr mem).regs kc = some K) :
    evalNode (tmFrame f tms fr mem) mem (.binary op' ty y kc) =
      (((tmFrame f tms fr mem).regs a).bind (·.as? ty)).map fun A => ⟨ty, A <<< s⟩ := by
  unfold shlPlan at h
  split at h
  · rename_i op ty' y0 k hn
    split at h
    · rename_i K0 hK0
      have hna := nodeAt_spec hn
      have hk0 : (tmFrame f tms fr mem).regs k = some K0 := tmVal_of_constOf hK0
      have hav : (tmFrame f tms fr mem).regs a =
          evalNode (tmFrame f tms fr mem) mem (.binary op ty' y0 k) := tmVal_node hna.1 hna.2
      split at h
      · cases h
      · rename_i hty
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
        subst hty
        split at h
        · rename_i hop
          simp only [beq_iff_eq] at hop
          subst hop
          split at h
          · rename_i hlt
            cases h
            have hlt8 : K0.bits.toNat % ty'.width + s < 2 ^ K0.ty.width :=
              Nat.lt_of_lt_of_le hlt (Nat.le_trans (width_le_128 ty')
                (Nat.le_trans (by decide : 128 ≤ 2 ^ 8) (Nat.pow_le_pow_right (by decide)
                  (width_ge_8 K0.ty))))
            rw [hav, evalNode_shift rfl, evalNode_shift rfl, hK, hk0]
            rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty') with _ | Y
            · rfl
            · simp [Sem.shift, Sem.ishl, Sem.shiftAmt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt8,
                Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hs, BitVec.shiftLeft_add]
          · cases h
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨hop, hk⟩, -⟩ := hc
            cases h
            have hks : K0.bits.toNat % ty'.width = s := by rw [hk]; exact Nat.mod_eq_of_lt hs
            rw [hav, evalNode_binary_nonShift rfl, hK]
            rcases hop with rfl | rfl
            · rw [evalNode_shift rfl, hk0]
              rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty') with _ | Y
              · rfl
              · simp [Sem.shift, Sem.ushr, Sem.shiftAmt, hks, Sem.binary, Sem.band,
                  BitVec.shiftLeft_ushiftRight]
            · rw [evalNode_shift rfl, hk0]
              rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty') with _ | Y
              · rfl
              · simp [Sem.shift, Sem.sshr, Sem.shiftAmt, hks, Sem.binary, Sem.band,
                  sshiftRight_shiftLeft]
          · cases h
    · cases h
  · cases h

theorem ruleSound_fam6Mul : RuleSound fam6Mul := by
  intro tms i x' h hord f fr mem t ht
  cases i with
  | binary op ty a b =>
    simp only [fam6Mul] at h
    obtain ⟨⟨a', s⟩, hm, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨op', y, K⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hk1, hk2⟩ := findTm_spec hkc
    have hK : (tmFrame f tms fr mem).regs kc = some K := by
      show tmVal f tms fr mem kc = _
      rw [tmVal_node hk1 hk2]
      rfl
    obtain ⟨rfl, hs, -, hval⟩ := mulShAmt_val hm
    rw [tmVal_node ht (hord t ht), hval, shlPlan_val hp hs hK]
  | _ => simp [fam6Mul] at h

/-! ## `reStep` -/

theorem reOp_spec {w : Nat} {op : BinaryOp} {k1 k2 c : BitVec w} (h : reOp op k1 k2 = some c) :
    op.isShift = false ∧ ∀ X : BitVec w, Sem.binary op (Sem.binary op X k1) k2 = Sem.binary op X c := by
  cases op <;> simp only [reOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    refine ⟨rfl, fun X => ?_⟩ <;>
    simp [Sem.binary, Sem.band, Sem.bor, Sem.bxor, Sem.imul, BitVec.and_assoc, BitVec.or_assoc,
      BitVec.xor_assoc, BitVec.mul_assoc]

/-- The node `rePlan` gives has the value of `op ty a b`. -/
theorem rePlan_val {tms : Array Tm} {op : BinaryOp} {ty : Ty} {a b x : Nat} {c : BitVec ty.width}
    (h : rePlan tms op ty a b = some (x, c)) :
    op.isShift = false ∧ ∀ (f : Function) (fr : Frame) (mem : Mem),
      evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) =
        (((tmFrame f tms fr mem).regs x).bind (·.as? ty)).map fun X => ⟨ty, Sem.binary op X c⟩ := by
  unfold rePlan at h
  split at h
  · rename_i k2 op' ty' x0 k hk2 hn
    have hna := nodeAt_spec hn
    split at h
    · cases h
    · rename_i hty
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
      subst hty
      split at h
      · rename_i hop
        simp only [beq_iff_eq] at hop
        subst hop
        obtain ⟨k1, hk1, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c', hc', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        obtain ⟨hns, hassoc⟩ := reOp_spec hc'
        refine ⟨hns, fun f fr mem => ?_⟩
        have hav : (tmFrame f tms fr mem).regs a =
            evalNode (tmFrame f tms fr mem) mem (.binary op' ty' x k) := tmVal_node hna.1 hna.2
        have hkv1 : (tmFrame f tms fr mem).regs k = some ⟨ty', k1⟩ := constAt_spec hk1
        have hkv2 : (tmFrame f tms fr mem).regs b = some ⟨ty', k2⟩ := constAt_spec hk2
        rw [evalNode_binary_nonShift hns, hav, evalNode_binary_nonShift hns, hkv1, hkv2]
        rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty') with _ | X
        · rfl
        · simp [hassoc]
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨K, hK, he⟩ := Option.map_eq_some_iff.1 h
          cases he
          refine ⟨rfl, fun f fr mem => ?_⟩
          have hav : (tmFrame f tms fr mem).regs a =
              evalNode (tmFrame f tms fr mem) mem (.binary .ishl ty' x k) :=
            tmVal_node hna.1 hna.2
          have hk : (tmFrame f tms fr mem).regs k = some K := tmVal_of_constOf hK
          have hkv2 : (tmFrame f tms fr mem).regs b = some ⟨ty', k2⟩ := constAt_spec hk2
          rw [evalNode_binary_nonShift rfl, hav, evalNode_shift rfl, hk, hkv2]
          rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty') with _ | X
          · rfl
          · simp only [Option.bind_some, Option.map_some, Sem.shift, Sem.ishl, Sem.shiftAmt,
              Val.as?_mk, Sem.binary, Sem.imul, BitVec.shiftLeft_eq_mul_twoPow]
            congr 2
            rw [BitVec.mul_assoc, BitVec.mul_comm (BitVec.twoPow _ _) k2]
        · cases h
  · cases h

theorem ruleSound_reStep : RuleSound reStep := by
  intro tms i x' h hord f fr mem t ht
  cases i with
  | binary op ty a b =>
    simp only [reStep] at h
    obtain ⟨⟨x, c⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hk1, hk2⟩ := findTm_spec hkc
    have hK : (tmFrame f tms fr mem).regs kc = some ⟨ty, c⟩ := by
      show tmVal f tms fr mem kc = _
      rw [tmVal_node hk1 hk2]
      rfl
    obtain ⟨hns, hval⟩ := rePlan_val hp
    rw [tmVal_node ht (hord t ht), hval, evalNode_binary_nonShift hns, hK]
    rcases ((tmFrame f tms fr mem).regs x).bind (·.as? ty) with _ | X <;> simp
  | _ => simp [reStep] at h

/-! ## The family -/

/-- **Family 6 is sound under typing.** -/
theorem ruleSoundT_fam6Step {f : Function} : RuleSoundT f (fam6Step (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  simp only [fam6Step] at h
  cases hs : shAmt (atomTy f) tms i with
  | some z =>
    rw [hs] at h
    cases h
    exact ruleSoundT_shAmt tms i _ hs hord fr mem t ht hA
  | none =>
    rw [hs] at h
    exact ruleSound_reStep tms i x' h hord f fr mem t ht

/-! ## The default normaliser -/

/-- **`Norm.base` is sound under typing.** -/
theorem normSoundT_base {f : Function} : NormSoundT f (Norm.base f) :=
  normSoundT_orElse
    (normSoundT_orElse
      (normSoundT_orElse (normSound_guard ruleSound_fam6Mul).toT normSound_std.toT)
      normSoundT_typed)
    (normSoundT_orElse (normSoundT_guard ruleSoundT_idStep)
      (normSoundT_orElse (normSound_guard ruleSound_affStep).toT
        (normSoundT_orElse (normSound_guard ruleSound_swapStep).toT
          (normSoundT_orElse (normSoundT_guard ruleSoundT_fam5Step)
            (normSoundT_guard ruleSoundT_fam6Step)))))

/-- **Every nesting depth of the narrowing is sound under typing.** -/
theorem normSoundT_narrowN {f : Function} : ∀ k, NormSoundT f (Norm.narrowN f k)
  | 0 => normSoundT_base
  | k + 1 => normSoundT_orElse normSoundT_base
      (normSoundT_guard (ruleSoundT_narrowStep (normSoundT_narrowN k)))

/-- **The validator's default normaliser is sound under typing.** -/
theorem normSoundT_stdT {f : Function} : NormSoundT f (Norm.stdT f) :=
  normSoundT_narrowN 3

end Opt.MidVal

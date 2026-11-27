import FV.Opt.Proof.MidValNormFam8

/-!
# Family 9: masks, narrowed shifts, complements, extensions, comparisons of extensions and of
`<=>`, `select` as min/max (#1119, agent MidendNext10)

`Norm.stdD f = Norm.orElse (Norm.guard fam8Step) (Norm.orElse (Norm.guard (fam9Step (atomTy
f))) (Norm.orElse (Norm.stdT f) (Norm.guard (dropStep (atomTy f)))))` (`FV/Opt/MidVal.lean`), the
validator's default normaliser. Each rule of `fam9Step` gives a node with the value of the node it
rewrites wherever the node's operands have values and the atoms below it are typed (`RuleSoundD`,
`FV/Opt/Proof/MidValNormDrop.lean`), proved against `Clif.evalInst`:

* `borMask` — `(x & y) | ~y = x | ~y` (`or_and_not`; `borMask_val`, in every frame,
  `FV/Opt/Proof/MidValNormFam4.lean`, where `narrowStep` uses it too);
* `notDec` — `~(x + -1) = -x`, `~(x - 1) = -x`, `~(~x + y) = x - y`, `~(y + ~x) = x - y`;
* `redShl` — the low `m` bits of `(ext x) << s` are `x << s` for `s < m` (`setWidth_ishl_ext`);
  `x` has its static type `ty` (`tyAt_val`);
* `redUn` — the low `m` bits of `-(ext x)` and `~(ext x)` are `-x` and `~x`;
* `extExt` — an extension of an extension (`uext_uext`, `sext_sext`, `sext_uext`);
* `extCmp` — a zero-extended `i32` is not negative at `i64` (`toInt_uext`); a sign extension
  compares with `0` as its operand does (`sext_cmp_zero`);
* `shipCmp` — `(x > y) - (x < y)` is `1`, `0` or `-1` (`ship_spec`);
* `selMinMax` — `select (x ? y) x y` and `select (x ? y) y x` are the min/max (`sel_mm`).

Main results: `ruleSoundD_fam9Step`, **`normSoundD_stdD : NormSoundD f (Norm.stdD f)`** (moved
here from `MidValNormFam8.lean`, statement unchanged).
-/

namespace Opt.MidVal

open Clif

/-! ## Values of the nodes involved -/

/-- A term that is a unary node with a value: its operand holds a value of its type. -/
theorem tmVal_un_ops {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {a : Nat}
    {op : UnaryOp} {ty : Ty} {x : Nat} (hA : nodeAt tms a = some (.unary op ty x))
    (hd : (tmVal f tms fr mem a).isSome) :
    ∃ X : BitVec ty.width, tmVal f tms fr mem x = some ⟨ty, X⟩ ∧
      tmVal f tms fr mem a = some ⟨ty, Sem.unary op X⟩ := by
  obtain ⟨hta, hoa⟩ := nodeAt_spec hA
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 hd
  have hv := hva
  rw [tmVal_node hta hoa] at hv
  obtain ⟨X, hX, rfl⟩ := (Opt.Proof.evalNode_unary _ mem).1 hv
  exact ⟨X, hX, hva⟩

/-- A term that is an extension with a value: its operand has a narrower value. -/
theorem tmVal_ext_ops {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {e : Nat}
    {op : ExtendOp} {ty : Ty} {x : Nat} (hE : nodeAt tms e = some (.extend op ty x))
    (hd : (tmVal f tms fr mem e).isSome) :
    ∃ v : Val, tmVal f tms fr mem x = some v ∧ v.ty.width < ty.width ∧
      tmVal f tms fr mem e = some ⟨ty, extOp op ty.width v.bits⟩ := by
  obtain ⟨hte, hoe⟩ := nodeAt_spec hE
  obtain ⟨ve, hve⟩ := Option.isSome_iff_exists.1 hd
  have hv := hve
  rw [tmVal_node hte hoe, evalNode_extend] at hv
  obtain ⟨v, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
  split at hv
  · rename_i hw
    cases hv
    exact ⟨v, hx, hw, hve⟩
  · cases hv

/-- A reachable term with a static type holds a value of that type. -/
theorem val_of_tyAt {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {i : Inst} {x : Nat}
    {ty : Ty} (hA : AtomsTyped f tms fr mem i) (hr : TmReach tms i x)
    (ht : tyAt (atomTy f) tms x = some ty) {v : Val} (hv : tmVal f tms fr mem x = some v) :
    ∃ X : BitVec ty.width, v = ⟨ty, X⟩ := by
  have hvt := tyAt_val hA hr ht hv
  obtain ⟨vt, X⟩ := v
  simp only at hvt
  subst hvt
  exact ⟨X, rfl⟩

/-- An extension to the width of its operand is the operand. -/
theorem extOp_self {w : Nat} (op : ExtendOp) (X : BitVec w) : extOp op w X = X := by
  cases op <;> simp [extOp, Sem.uextend, Sem.sextend]

/-! ## `notDec` -/

theorem one_eq_ofNat {w : Nat} : (1#w : BitVec w) = 1 := rfl

theorem not_eq_neg_sub {w : Nat} (Z : BitVec w) : ~~~Z = -Z - 1 := by
  rw [BitVec.neg_eq_not_add Z, one_eq_ofNat, BitVec.add_sub_cancel]

theorem not_add_neg_one {w : Nat} (X : BitVec w) : ~~~(X + -1) = -X := by
  rw [not_eq_neg_sub (X + -1), BitVec.neg_add, BitVec.sub_eq_add_neg (-X) (-1), BitVec.neg_neg,
    BitVec.add_sub_cancel]

theorem not_sub_one {w : Nat} (X : BitVec w) : ~~~(X - 1) = -X := by
  rw [BitVec.sub_eq_add_neg, not_add_neg_one]

theorem not_not_add {w : Nat} (X Y : BitVec w) : ~~~(~~~X + Y) = X - Y := by
  rw [not_eq_neg_sub (~~~X + Y), BitVec.neg_add, BitVec.neg_eq_not_add (~~~X), BitVec.not_not,
    one_eq_ofNat, BitVec.sub_eq_add_neg (X + 1) Y, BitVec.sub_eq_add_neg (X + 1 + -Y) 1,
    BitVec.sub_eq_add_neg X Y, show X + 1 + -Y + -1 = X + -Y + (1 + -1) by ac_rfl,
    ← BitVec.sub_eq_add_neg 1 1, BitVec.sub_self, BitVec.add_zero]

theorem not_add_not {w : Nat} (X Y : BitVec w) : ~~~(Y + ~~~X) = X - Y := by
  rw [BitVec.add_comm Y, not_not_add]

theorem notAddPick_spec {tms : Array Tm} {ty : Ty} {p q : Nat} {x' : Tm}
    (h : notAddPick tms ty p q = some x') :
    ∃ x, nodeAt tms p = some (.unary .bnot ty x) ∧ x' = .node (.binary .isub ty x q) := by
  unfold notAddPick at h
  split at h
  · rename_i tp x hp
    split at h
    · rename_i htp
      have htp' : tp = ty := by simpa using htp
      subst htp'
      cases h
      exact ⟨x, hp, rfl⟩
    · cases h
  · cases h

theorem notDec_spec {tms : Array Tm} {ty : Ty} {a : Nat} {x' : Tm}
    (h : notDec tms ty a = some x') :
    (∃ p q, nodeAt tms a = some (.binary .iadd ty p q) ∧ constAt tms ty q = some (-1) ∧
        x' = .node (.unary .ineg ty p)) ∨
      (∃ p q, nodeAt tms a = some (.binary .iadd ty p q) ∧ notAddPick tms ty p q = some x') ∨
      (∃ p q, nodeAt tms a = some (.binary .iadd ty p q) ∧ notAddPick tms ty q p = some x') ∨
      (∃ x k, nodeAt tms a = some (.binary .isub ty x k) ∧ constAt tms ty k = some 1 ∧
        x' = .node (.unary .ineg ty x)) := by
  unfold notDec at h
  split at h
  · rename_i ty' p q hA
    split at h
    · cases h
    · rename_i hty
      have hty' : ty' = ty := by simpa using hty
      subst hty'
      split at h
      · rename_i hq
        cases h
        exact .inl ⟨p, q, hA, by simpa using hq, rfl⟩
      · cases h1 : notAddPick tms ty' p q with
        | some y =>
          rw [h1] at h
          cases h
          exact .inr (.inl ⟨p, q, hA, h1⟩)
        | none =>
          rw [h1] at h
          simp only [Option.orElse_none] at h
          exact .inr (.inr (.inl ⟨p, q, hA, h⟩))
  · rename_i ty' x k hA
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hk⟩ := hc
      cases h
      exact .inr (.inr (.inr ⟨x, k, hA, hk, rfl⟩))
    · cases h
  · cases h

/-- `bnot ty a` with `a = iadd ty p q` and `p = bnot ty x`: `isub ty x q`. -/
theorem notAdd_val {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {ty : Ty}
    {a p q x : Nat} (hA : nodeAt tms a = some (.binary .iadd ty p q))
    (hP : nodeAt tms p = some (.unary .bnot ty x)) (hd : (tmVal f tms fr mem a).isSome) :
    evalNode (tmFrame f tms fr mem) mem (.binary .isub ty x q) =
      evalNode (tmFrame f tms fr mem) mem (.unary .bnot ty a) := by
  obtain ⟨P, Q, hPv, hQv, ha⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA hd
  obtain ⟨X, hX, hp⟩ := tmVal_un_ops (f := f) (fr := fr) (mem := mem) hP (by rw [hPv]; rfl)
  have hPX : P = ~~~X := val_bits_eq (hPv.symm.trans hp)
  subst hPX
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
  have hQ' : (tmFrame f tms fr mem).regs q = some ⟨ty, Q⟩ := hQv
  have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary .iadd (~~~X) Q⟩ := ha
  rw [evalNode_bin_of rfl hX' hQ', evalNode_unary, ha']
  simp [Sem.binary, Sem.isub, Sem.iadd, Sem.unary, Sem.bnot, not_not_add]

theorem ruleSoundD_notDec {f : Function} {ty : Ty} {a : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), notDec tms ty a = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.unary .bnot ty a), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.unary .bnot ty a) := by
  intro tms x' h hord fr mem t ht hd
  have hda := hd a (by simp [operands])
  rcases notDec_spec h with ⟨p, q, hA, hq, rfl⟩ | ⟨p, q, hA, h1⟩ | ⟨p, q, hA, h1⟩ |
      ⟨x, k, hA, hk, rfl⟩
  · obtain ⟨P, Q, hPv, hQv, ha⟩ := tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA hda
    have hQ1 : Q = -1 := (val_bits_eq ((constAt_spec hq).symm.trans hQv)).symm
    subst hQ1
    have hP' : (tmFrame f tms fr mem).regs p = some ⟨ty, P⟩ := hPv
    have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary .iadd P (-1)⟩ := ha
    rw [tmVal_node' ht (hord t ht), evalNode_unary, evalNode_unary, hP', ha']
    simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.unary, Sem.binary, Sem.iadd,
      Sem.bnot, Sem.ineg, not_add_neg_one]
  · obtain ⟨x, hP, rfl⟩ := notAddPick_spec h1
    rw [tmVal_node' ht (hord t ht)]
    exact notAdd_val hA hP hda
  · obtain ⟨x, hQ, rfl⟩ := notAddPick_spec h1
    obtain ⟨P, Q, hPv, hQv, ha⟩ := tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA hda
    obtain ⟨X, hX, hq⟩ := tmVal_un_ops (f := f) (fr := fr) (mem := mem) hQ (by rw [hQv]; rfl)
    have hQX : Q = ~~~X := val_bits_eq (hQv.symm.trans hq)
    subst hQX
    have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
    have hP' : (tmFrame f tms fr mem).regs p = some ⟨ty, P⟩ := hPv
    have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary .iadd P (~~~X)⟩ := ha
    rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hX' hP', evalNode_unary, ha']
    simp [Sem.binary, Sem.isub, Sem.iadd, Sem.unary, Sem.bnot, not_add_not]
  · obtain ⟨X, K, hXv, hKv, ha⟩ := tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA hda
    have hK1 : K = 1 := (val_bits_eq ((constAt_spec hk).symm.trans hKv)).symm
    subst hK1
    have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hXv
    have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary .isub X 1⟩ := ha
    rw [tmVal_node' ht (hord t ht), evalNode_unary, evalNode_unary, hX', ha']
    simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.unary, Sem.binary, Sem.isub,
      Sem.bnot, Sem.ineg, not_sub_one]

/-! ## `redShl` -/

/-- Truncation commutes with a left shift. -/
theorem setWidth_shl {W m : Nat} (Z : BitVec W) (s : Nat) (hm : m ≤ W) :
    BitVec.setWidth m (Z <<< s) = BitVec.setWidth m Z <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiW : i < W := by omega
  have his : i - s < m := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, hiW, his, decide_true,
    Bool.true_and]

/-- The low `m` bits of `ext X << s`, `s = K mod W` below `m`, are `X << s`. -/
theorem setWidth_ishl_ext {m W v : Nat} (op : ExtendOp) (X : BitVec m) (K : BitVec v)
    (hm : m < W) (hs : K.toNat % W < m) :
    BitVec.setWidth m (Sem.ishl (extOp op W X) K) =
      Sem.ishl X (BitVec.ofNat m (K.toNat % W)) := by
  have h1 : (BitVec.ofNat m (K.toNat % W)).toNat % m = K.toNat % W := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hs Nat.lt_two_pow_self),
      Nat.mod_eq_of_lt hs]
  simp only [Sem.ishl, Sem.shiftAmt]
  rw [h1, setWidth_shl _ _ (Nat.le_of_lt hm), setWidth_extOp op X (Nat.le_of_lt hm),
    extOp_self]

theorem redShlPlan_spec {aty : Tm → Option Ty} {tms : Array Tm} {ty : Ty} {u x s : Nat}
    (h : redShlPlan aty tms ty u = some (x, s)) :
    ∃ wty e k op K, nodeAt tms u = some (.binary .ishl wty e k) ∧
      nodeAt tms e = some (.extend op wty x) ∧ constOf tms k = some K ∧ ty.width < wty.width ∧
      tyAt aty tms x = some ty ∧ s = K.bits.toNat % wty.width ∧ s < ty.width := by
  unfold redShlPlan at h
  split at h
  · rename_i wty e k hU
    split at h
    · rename_i op ety x0 K hE hK
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨rfl, hw⟩, htx⟩, hs⟩ := hc
        cases h
        exact ⟨ety, e, k, op, K, hU, hE, hK, hw, htx, rfl, hs⟩
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_redShl {f : Function} {ty : Ty} {u : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), redShl (atomTy f) tms ty u = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.ireduce ty u) →
        (∀ o ∈ operands (.ireduce ty u), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.ireduce ty u) := by
  intro tms x' h hord fr mem t ht hA hd
  unfold redShl at h
  obtain ⟨⟨x, s⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  have hV : (tmFrame f tms fr mem).regs kc = some ⟨ty, BitVec.ofNat ty.width s⟩ :=
    tmVal_findConst hkc
  obtain ⟨wty, e, k, op, K, hU, hE, hK, hw, htx, rfl, hs⟩ := redShlPlan_spec hp
  obtain ⟨htu, hou⟩ := nodeAt_spec hU
  obtain ⟨hte, hoe⟩ := nodeAt_spec hE
  have hru : TmReach tms (.ireduce ty u) u := .op (by simp [operands])
  have hre : TmReach tms (.ireduce ty u) e := .sub hru htu (by simp [operands])
  have hrx : TmReach tms (.ireduce ty u) x := .sub hre hte (by simp [operands])
  -- the shift's value
  obtain ⟨vu, hvu⟩ := Option.isSome_iff_exists.1 (hd u (by simp [operands]))
  have hvu' := hvu
  rw [tmVal_node htu hou] at hvu'
  have hsh := (Opt.Proof.evalNode_binary_iff _ mem).1 hvu'
  simp only [BinaryOp.isShift, ite_true] at hsh
  obtain ⟨E, hEv, c, hc, r, hr, rfl⟩ := hsh
  have hKv : tmVal f tms fr mem k = some K := tmVal_of_constOf hK
  have hcK : c = K := by
    have := hc.symm.trans hKv
    simpa using this
  subst hcK
  simp only [Sem.shift, Option.some.injEq] at hr
  subst hr
  -- the extension's value
  obtain ⟨v, hxv, hvw, hev⟩ :=
    tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE (by rw [show tmVal f tms fr mem e = _ from hEv]; rfl)
  obtain ⟨X, rfl⟩ := val_of_tyAt hA hrx htx hxv
  have hEX : E = extOp op wty.width X := val_bits_eq ((show tmVal f tms fr mem e = _ from hEv).symm.trans hev)
  subst hEX
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hxv
  have hu' : (tmFrame f tms fr mem).regs u = some ⟨wty, Sem.ishl (extOp op wty.width X) c.bits⟩ :=
    hvu
  rw [tmVal_node' ht (hord t ht), evalNode_ishl hV, hX', evalNode_ireduce, hu']
  simp only [Option.bind_some, Val.as?_mk, Option.map_some, hw, if_true]
  rw [setWidth_ishl_ext op X c.bits hw hs]

/-! ## `redUn` -/

theorem setWidth_unary_ext {m W : Nat} {op : UnaryOp} (hop : op = .ineg ∨ op = .bnot)
    (op' : ExtendOp) (X : BitVec m) (hm : m < W) :
    BitVec.setWidth m (Sem.unary op (extOp op' W X)) = Sem.unary op X := by
  rcases hop with rfl | rfl
  · simp only [Sem.unary, Sem.ineg]
    rw [BitVec.setWidth_neg_of_le (Nat.le_of_lt hm), setWidth_extOp op' X (Nat.le_of_lt hm),
      extOp_self]
  · simp only [Sem.unary, Sem.bnot]
    rw [BitVec.setWidth_not (Nat.le_of_lt hm), setWidth_extOp op' X (Nat.le_of_lt hm), extOp_self]

theorem redUn_spec {aty : Tm → Option Ty} {tms : Array Tm} {ty : Ty} {u : Nat} {x' : Tm}
    (h : redUn aty tms ty u = some x') :
    ∃ op wty e op' x, nodeAt tms u = some (.unary op wty e) ∧ (op = .ineg ∨ op = .bnot) ∧
      nodeAt tms e = some (.extend op' wty x) ∧ ty.width < wty.width ∧
      tyAt aty tms x = some ty ∧ x' = .node (.unary op ty x) := by
  unfold redUn at h
  split at h
  · rename_i op wty e hU
    split at h
    · rename_i hop
      simp only [Bool.or_eq_true, beq_iff_eq] at hop
      split at h
      · rename_i op' ety x hE
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          obtain ⟨⟨rfl, hw⟩, htx⟩ := hc
          cases h
          exact ⟨op, ety, e, op', x, hU, hop, hE, hw, htx, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_redUn {f : Function} {ty : Ty} {u : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), redUn (atomTy f) tms ty u = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.ireduce ty u) →
        (∀ o ∈ operands (.ireduce ty u), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.ireduce ty u) := by
  intro tms x' h hord fr mem t ht hA hd
  obtain ⟨op, wty, e, op', x, hU, hop, hE, hw, htx, rfl⟩ := redUn_spec h
  obtain ⟨htu, _⟩ := nodeAt_spec hU
  obtain ⟨hte, _⟩ := nodeAt_spec hE
  have hru : TmReach tms (.ireduce ty u) u := .op (by simp [operands])
  have hre : TmReach tms (.ireduce ty u) e := .sub hru htu (by simp [operands])
  have hrx : TmReach tms (.ireduce ty u) x := .sub hre hte (by simp [operands])
  obtain ⟨E, hEv, hu⟩ :=
    tmVal_un_ops (f := f) (fr := fr) (mem := mem) hU (hd u (by simp [operands]))
  obtain ⟨v, hxv, _, hev⟩ := tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE (by rw [hEv]; rfl)
  obtain ⟨X, rfl⟩ := val_of_tyAt hA hrx htx hxv
  have hEX : E = extOp op' wty.width X := val_bits_eq (hEv.symm.trans hev)
  subst hEX
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hxv
  have hu' : (tmFrame f tms fr mem).regs u = some ⟨wty, Sem.unary op (extOp op' wty.width X)⟩ := hu
  rw [tmVal_node' ht (hord t ht), evalNode_unary, hX', evalNode_ireduce, hu']
  simp only [Option.bind_some, Val.as?_mk, Option.map_some, hw, if_true]
  rw [setWidth_unary_ext hop op' X hw]

/-! ## `extExt` -/

theorem uext_uext {w V W : Nat} (X : BitVec w) (h1 : w < V) :
    Sem.uextend W (Sem.uextend V X) = Sem.uextend W X := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sem.uextend, BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]
  by_cases hiV : i < V
  · simp [hiV]
  · simp [hiV, BitVec.getLsbD_of_ge X i (by omega)]

theorem sext_sext {w V W : Nat} (X : BitVec w) (h1 : w < V) (h2 : V < W) :
    Sem.sextend W (Sem.sextend V X) = Sem.sextend W X := by
  apply BitVec.eq_of_toInt_eq
  simp only [Sem.sextend]
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_signExtend_of_le (by omega),
    BitVec.toInt_signExtend_of_le (by omega)]

/-- A zero extension to a wider type is not negative: its `toInt` is its operand's `toNat`. -/
theorem toInt_uext {w V : Nat} (X : BitVec w) (h : w < V) : (Sem.uextend V X).toInt = X.toNat := by
  have hx := X.isLt
  have hp : 2 * 2 ^ w ≤ 2 ^ V := by
    rw [← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by omega) h
  have hlt : X.toNat < 2 ^ V := by omega
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [Sem.uextend, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hlt]
  rw [if_pos (by omega)]

theorem sext_uext {w V W : Nat} (X : BitVec w) (h1 : w < V) (h2 : V < W) :
    Sem.sextend W (Sem.uextend V X) = Sem.uextend W X := by
  apply BitVec.eq_of_toInt_eq
  simp only [Sem.sextend]
  rw [BitVec.toInt_signExtend_of_le (by omega), toInt_uext X h1, toInt_uext X (by omega)]

theorem extExt_spec {tms : Array Tm} {op : ExtendOp} {ty : Ty} {u : Nat} {x' : Tm}
    (h : extExt tms op ty u = some x') :
    ∃ op2 ty2 x, nodeAt tms u = some (.extend op2 ty2 x) ∧ ty2.width < ty.width ∧
      ((op2 = .uextend ∧ x' = .node (.extend .uextend ty x)) ∨
        (op = .sextend ∧ op2 = .sextend ∧ x' = .node (.extend .sextend ty x))) := by
  unfold extExt at h
  split at h
  · rename_i op2 ty2 x hU
    split at h
    · rename_i hw
      refine ⟨op2, ty2, x, hU, hw, ?_⟩
      cases op <;> cases op2 <;> simp at h
      · exact .inl ⟨rfl, h.symm⟩
      · exact .inl ⟨rfl, h.symm⟩
      · exact .inr ⟨rfl, rfl, h.symm⟩
    · cases h
  · cases h

theorem ruleSoundD_extExt {f : Function} {op : ExtendOp} {ty : Ty} {u : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), extExt tms op ty u = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.extend op ty u), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.extend op ty u) := by
  intro tms x' h hord fr mem t ht hd
  obtain ⟨op2, ty2, x, hU, hw, hcase⟩ := extExt_spec h
  obtain ⟨v, hxv, hvw, hu⟩ :=
    tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hU (hd u (by simp [operands]))
  have hx' : (tmFrame f tms fr mem).regs x = some v := hxv
  have hu' : (tmFrame f tms fr mem).regs u = some ⟨ty2, extOp op2 ty2.width v.bits⟩ := hu
  have hvw' : v.ty.width < ty.width := Nat.lt_trans hvw hw
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [tmVal_node' ht (hord t ht), evalNode_extend, evalNode_extend, hx', hu']
    simp only [Option.bind_some, hvw', hw, if_true, Option.some.injEq, Val.mk.injEq, heq_eq_eq,
      true_and]
    cases op <;> simp only [extOp]
    · exact (uext_uext v.bits hvw).symm
    · exact (sext_uext v.bits hvw hw).symm
  · rw [tmVal_node' ht (hord t ht), evalNode_extend, evalNode_extend, hx', hu']
    simp only [Option.bind_some, hvw', hw, if_true, Option.some.injEq, Val.mk.injEq, heq_eq_eq,
      true_and, extOp]
    exact (sext_sext v.bits hvw hw).symm

/-! ## `extCmp` -/

theorem sext_cmp_zero {w W : Nat} {cc : IntCC} (hcc : sextCC cc = true) (X : BitVec w)
    (h : w < W) : Sem.intcc cc (Sem.sextend W X) 0 = Sem.intcc cc X 0 := by
  have hi : (Sem.sextend W X).toInt = X.toInt := BitVec.toInt_signExtend_of_le (Nat.le_of_lt h)
  have hz1 : (0 : BitVec W).toInt = 0 := BitVec.toInt_zero
  have hz2 : (0 : BitVec w).toInt = 0 := BitVec.toInt_zero
  have heq : (Sem.sextend W X == 0) = (X == 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toInt_inj, ← BitVec.toInt_inj (x := X),
      hi, hz1, hz2]
  cases cc <;> simp only [sextCC, Bool.false_eq_true] at hcc <;>
    simp only [Sem.intcc, BitVec.slt, BitVec.sle, hi, hz1, hz2, bne, heq]

theorem extCmpPlan_spec {aty : Tm → Option Ty} {tms : Array Tm} {cc : IntCC} {ty : Ty}
    {a b : Nat} {r : BitVec 8 ⊕ (Ty × Nat)} (h : extCmpPlan aty tms cc ty a b = some r) :
    (∃ x, nodeAt tms a = some (.extend .uextend .i64 x) ∧ ty = .i64 ∧
        constAt tms ty b = some 0 ∧ tyAt aty tms x = some .i32 ∧
        ((cc = .slt ∧ r = .inl 0) ∨ (cc = .sge ∧ r = .inl 1))) ∨
      (∃ x xt, nodeAt tms a = some (.extend .sextend ty x) ∧ constAt tms ty b = some 0 ∧
        sextCC cc = true ∧ tyAt aty tms x = some xt ∧ r = .inr (xt, x)) := by
  unfold extCmpPlan at h
  split at h
  · rename_i ety x z hA hb
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, htx⟩ := hc
      refine .inl ⟨x, hA, rfl, hb, htx, ?_⟩
      split at h
      · rename_i hcc
        cases h
        exact .inl ⟨by simpa using hcc, rfl⟩
      · split at h
        · rename_i _ hcc
          cases h
          exact .inr ⟨by simpa using hcc, rfl⟩
        · cases h
    · cases h
  · rename_i ety x z hA hb
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, hcc⟩ := hc
      obtain ⟨xt, hxt, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
        exact .inr ⟨x, xt, hA, hb, hcc, hxt, rfl⟩
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_extCmp {f : Function} {cc : IntCC} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), extCmp (atomTy f) tms cc ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.icmp cc ty a b) →
        (∀ o ∈ operands (.icmp cc ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.icmp cc ty a b) := by
  intro tms x' h hord fr mem t ht hA hd
  unfold extCmp at h
  split at h
  · rename_i v hp
    cases h
    rcases extCmpPlan_spec hp with ⟨x, hE, rfl, hb, htx, hcc⟩ | ⟨x, xt, _, _, _, _, hr⟩
    · obtain ⟨hte, _⟩ := nodeAt_spec hE
      have hra : TmReach tms (.icmp cc .i64 a b) a := .op (by simp [operands])
      have hrx : TmReach tms (.icmp cc .i64 a b) x := .sub hra hte (by simp [operands])
      obtain ⟨u, hxv, _, hav⟩ :=
        tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE (hd a (by simp [operands]))
      obtain ⟨X, rfl⟩ := val_of_tyAt hA hrx htx hxv
      have ha' : (tmFrame f tms fr mem).regs a =
          some ⟨.i64, extOp .uextend Ty.i64.width X⟩ := hav
      have hb' : (tmFrame f tms fr mem).regs b = some ⟨.i64, 0⟩ := constAt_spec hb
      have hnn := toInt_uext X (show Ty.i32.width < Ty.i64.width by decide)
      have hz : (0 : BitVec Ty.i64.width).toInt = 0 := BitVec.toInt_zero
      have hslt : Sem.intcc .slt (extOp .uextend Ty.i64.width X) 0 = false := by
        simp only [Sem.intcc, extOp, BitVec.slt, hnn, hz, decide_eq_false_iff_not]
        omega
      have hsge : Sem.intcc .sge (extOp .uextend Ty.i64.width X) 0 = true := by
        simp only [Sem.intcc, extOp, BitVec.sle, hnn, hz, decide_eq_true_eq]
        omega
      rw [tmVal_node' ht (by simp [Tm.ops, operands]), evalNode_icmp_of ha' hb']
      rcases hcc with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;> cases hv
      · show some (Val.mk .i8 0) =
          some (Val.mk .i8 (Sem.icmp .slt (extOp .uextend Ty.i64.width X) 0))
        simp only [Sem.icmp, hslt]
        rfl
      · show some (Val.mk .i8 1) =
          some (Val.mk .i8 (Sem.icmp .sge (extOp .uextend Ty.i64.width X) 0))
        simp only [Sem.icmp, hsge]
        rfl
    · cases hr
  · rename_i xt x hp
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases extCmpPlan_spec hp with ⟨_, _, _, _, _, hcc⟩ | ⟨x0, xt0, hE, hb, hcc, htx, hr⟩
    · rcases hcc with ⟨_, hr⟩ | ⟨_, hr⟩ <;> cases hr
    · cases hr
      obtain ⟨hte, _⟩ := nodeAt_spec hE
      have hra : TmReach tms (.icmp cc ty a b) a := .op (by simp [operands])
      have hrx : TmReach tms (.icmp cc ty a b) x := .sub hra hte (by simp [operands])
      obtain ⟨u, hxv, huw, hav⟩ :=
        tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE (hd a (by simp [operands]))
      obtain ⟨X, rfl⟩ := val_of_tyAt hA hrx htx hxv
      have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, extOp .sextend ty.width X⟩ := hav
      have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, 0⟩ := constAt_spec hb
      have hX' : (tmFrame f tms fr mem).regs x = some ⟨xt, X⟩ := hxv
      have hZ : (tmFrame f tms fr mem).regs z = some ⟨xt, 0⟩ := tmVal_findConst hz
      rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hX' hZ, evalNode_icmp_of ha' hb']
      simp only [Sem.icmp, extOp, sext_cmp_zero hcc X huw]
  · cases h

/-! ## `shipCmp` -/

/-- The three outcomes of comparing two values (`sg`: signed). -/
theorem ship_cases {w : Nat} (sg : Bool) (X Y : BitVec w) :
    (Sem.intcc (if sg then .slt else .ult) X Y = true ∧
        Sem.intcc (if sg then .sgt else .ugt) X Y = false ∧ (X == Y) = false) ∨
      (Sem.intcc (if sg then .slt else .ult) X Y = false ∧
        Sem.intcc (if sg then .sgt else .ugt) X Y = true ∧ (X == Y) = false) ∨
      (Sem.intcc (if sg then .slt else .ult) X Y = false ∧
        Sem.intcc (if sg then .sgt else .ugt) X Y = false ∧ (X == Y) = true) := by
  cases sg
  · simp only [Bool.false_eq_true, ite_false, Sem.intcc, BitVec.ult, decide_eq_true_eq,
      decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
    rcases Nat.lt_trichotomy X.toNat Y.toNat with h | h | h
    · exact .inl ⟨h, by omega, fun e => by subst e; omega⟩
    · exact .inr (.inr ⟨by omega, by omega, BitVec.eq_of_toNat_eq h⟩)
    · exact .inr (.inl ⟨by omega, h, fun e => by subst e; omega⟩)
  · simp only [ite_true, Sem.intcc, BitVec.slt, decide_eq_true_eq, decide_eq_false_iff_not,
      beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
    rcases Int.lt_trichotomy X.toInt Y.toInt with h | h | h
    · exact .inl ⟨h, by omega, fun e => by subst e; omega⟩
    · exact .inr (.inr ⟨by omega, by omega, BitVec.eq_of_toInt_eq h⟩)
    · exact .inr (.inl ⟨by omega, h, fun e => by subst e; omega⟩)

/-- `le`/`ge` are `lt`/`gt` or equal. -/
theorem ship_le {w : Nat} (sg : Bool) (X Y : BitVec w) :
    Sem.intcc (if sg then .sle else .ule) X Y =
      (Sem.intcc (if sg then .slt else .ult) X Y || (X == Y)) ∧
    Sem.intcc (if sg then .sge else .uge) X Y =
      (Sem.intcc (if sg then .sgt else .ugt) X Y || (X == Y)) := by
  cases sg
  · simp only [Bool.false_eq_true, ite_false, Sem.intcc, BitVec.ult, BitVec.ule]
    constructor
    · rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ← BitVec.toNat_inj]
      omega
    · rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ← BitVec.toNat_inj]
      omega
  · simp only [ite_true, Sem.intcc, BitVec.slt, BitVec.sle]
    constructor
    · rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ← BitVec.toInt_inj]
      omega
    · rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, ← BitVec.toInt_inj]
      omega

theorem ship_spec {w : Nat} {sg : Bool} {cc cc' : IntCC} {k : BitVec 8}
    (h : shipCC sg cc k = some cc') (X Y : BitVec w) :
    Sem.intcc cc (Sem.bool8 (Sem.intcc (if sg then .sgt else .ugt) X Y) -
      Sem.bool8 (Sem.intcc (if sg then .slt else .ult) X Y)) k = Sem.intcc cc' X Y := by
  have hcs := ship_cases sg X Y
  obtain ⟨hle, hge⟩ := ship_le sg X Y
  have hne : Sem.intcc .ne X Y = !(X == Y) := rfl
  have heq : Sem.intcc .eq X Y = (X == Y) := rfl
  -- the constant is `0`, `-1` or `1`
  have hk : (k = 0 ∧ shipCC sg cc (0 : BitVec 8) = some cc') ∨
      (k = -1 ∧ shipCC sg cc (-1 : BitVec 8) = some cc') ∨
      (k = 1 ∧ shipCC sg cc (1 : BitVec 8) = some cc') := by
    by_cases h0 : k = 0
    · subst h0
      exact .inl ⟨rfl, h⟩
    by_cases h1 : k = -1
    · subst h1
      exact .inr (.inl ⟨rfl, h⟩)
    by_cases h2 : k = 1
    · subst h2
      exact .inr (.inr ⟨rfl, h⟩)
    exfalso
    have e0 : (k == 0) = false := by simpa using h0
    have e1 : (k == -1) = false := by simpa using h1
    have e2 : (k == 1) = false := by simpa using h2
    unfold shipCC at h
    simp only [e0, e1, e2, Bool.false_eq_true, ite_false] at h
    cases h
  cases sg <;> (
    simp only [Bool.false_eq_true, ite_false, ite_true, eq_self_iff_true, ↓reduceIte] at hle hge hcs ⊢
    rcases hcs with ⟨hl, hg, he⟩ | ⟨hl, hg, he⟩ | ⟨hl, hg, he⟩ <;>
    rcases hk with ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ <;>
    cases cc <;> simp (config := { decide := true }) [shipCC, shipCC0, shipCCm, shipCCp, ordCC] at hc <;>
    subst hc <;>
    simp only [hl, hg, hle, hge, hne, heq, he] <;> decide)

theorem shipSg_spec {gc lc : IntCC} {sg : Bool} (h : shipSg gc lc = some sg) :
    gc = (if sg then .sgt else .ugt) ∧ lc = (if sg then .slt else .ult) := by
  unfold shipSg at h
  split at h <;> cases h <;> simp

theorem shipCmp_spec {tms : Array Tm} {cc : IntCC} {ty : Ty} {a b : Nat} {x' : Tm}
    (h : shipCmp tms cc ty a b = some x') :
    ∃ g l rty x y k sg cc', ty = .i8 ∧ nodeAt tms a = some (.binary .isub .i8 g l) ∧
      constAt tms .i8 b = some k ∧
      nodeAt tms g = some (.icmp (if sg then .sgt else .ugt) rty x y) ∧
      nodeAt tms l = some (.icmp (if sg then .slt else .ult) rty x y) ∧
      shipCC sg cc k = some cc' ∧ x' = .node (.icmp cc' rty x y) := by
  unfold shipCmp at h
  split at h
  · cases h
  · rename_i hty
    have hty' : ty = .i8 := by simpa using hty
    subst hty'
    split at h
    · rename_i sty g l k hA hb
      split at h
      · cases h
      · rename_i hsty
        have hsty' : sty = .i8 := by simpa using hsty
        subst hsty'
        split at h
        · rename_i gc rty x y lc rty' x' y' hG hL
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
            obtain ⟨sg, hsg, h⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨cc', hcc, rfl⟩ := Option.map_eq_some_iff.1 h
            obtain ⟨rfl, rfl⟩ := shipSg_spec hsg
            exact ⟨g, l, rty, x, y, k, sg, cc', rfl, hA, hb, hG, hL, hcc, rfl⟩
          · cases h
        · cases h
    · cases h

theorem ruleSoundD_shipCmp {f : Function} {cc : IntCC} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), shipCmp tms cc ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.icmp cc ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.icmp cc ty a b) := by
  intro tms x' h hord fr mem t ht hd
  obtain ⟨g, l, rty, x, y, k, sg, cc', rfl, hA, hb, hG, hL, hcc, rfl⟩ := shipCmp_spec h
  obtain ⟨Gv, Lv, hGv, hLv, _⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
  obtain ⟨hta, hoa⟩ := nodeAt_spec hA
  obtain ⟨htg, hog⟩ := nodeAt_spec hG
  obtain ⟨htl, hol⟩ := nodeAt_spec hL
  have hg := hGv
  rw [tmVal_node htg hog] at hg
  obtain ⟨X, Y, hX, hY, _⟩ := (Opt.Proof.evalNode_icmp _ mem).1 hg
  have hg' : (tmFrame f tms fr mem).regs g =
      some ⟨.i8, Sem.icmp (if sg then .sgt else .ugt) X Y⟩ := by
    show tmVal f tms fr mem g = _
    rw [tmVal_node htg hog, evalNode_icmp_of hX hY]
  have hl' : (tmFrame f tms fr mem).regs l =
      some ⟨.i8, Sem.icmp (if sg then .slt else .ult) X Y⟩ := by
    show tmVal f tms fr mem l = _
    rw [tmVal_node htl hol, evalNode_icmp_of hX hY]
  have ha' : (tmFrame f tms fr mem).regs a = some ⟨.i8, Sem.binary .isub
      (Sem.icmp (if sg then .sgt else .ugt) X Y) (Sem.icmp (if sg then .slt else .ult) X Y)⟩ := by
    show tmVal f tms fr mem a = _
    rw [tmVal_node hta hoa, evalNode_bin_of rfl hg' hl']
  have hb' : (tmFrame f tms fr mem).regs b = some ⟨.i8, k⟩ := constAt_spec hb
  rw [tmVal_node' ht (hord t ht), evalNode_icmp_of hX hY, evalNode_icmp_of ha' hb']
  exact congrArg (fun r => some (Val.mk .i8 (Sem.bool8 r))) (ship_spec hcc X Y).symm

/-! ## `selMinMax` -/

theorem sel_mm {w : Nat} {cc : IntCC} {sw : Bool} {op : BinaryOp} (h : mmOp cc sw = some op)
    (A B : BitVec w) :
    Sem.select (Sem.icmp cc A B) (if sw then B else A) (if sw then A else B) =
      Sem.binary op A B := by
  simp only [Sem.icmp, select_bool8]
  cases cc <;> cases sw <;> simp only [mmOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Sem.intcc, Sem.binary, Sem.umin, Sem.umax, Sem.smin, Sem.smax, BitVec.ult,
      BitVec.ule, BitVec.slt, BitVec.sle, Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> split <;>
    first
      | rfl
      | (rename_i h1 h2
         simp only [decide_eq_true_eq] at h1 h2
         first
           | (apply BitVec.eq_of_toNat_eq; omega)
           | (apply BitVec.eq_of_toInt_eq; omega))

theorem selMinMax_spec {tms : Array Tm} {ty : Ty} {c x y : Nat} {x' : Tm}
    (h : selMinMax tms ty c x y = some x') :
    ∃ cc a b sw op, nodeAt tms c = some (.icmp cc ty a b) ∧ mmOp cc sw = some op ∧
      x = (if sw then b else a) ∧ y = (if sw then a else b) ∧
      x' = .node (.binary op ty a b) := by
  unfold selMinMax at h
  split at h
  · rename_i cc cty a b hC
    split at h
    · cases h
    · rename_i hty
      have hty' : cty = ty := by simpa using hty
      subst hty'
      split at h
      · rename_i hab
        simp only [Bool.and_eq_true, beq_iff_eq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        obtain ⟨op, hop, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨cc, a, b, false, op, hC, hop, rfl, rfl, rfl⟩
      · split at h
        · rename_i _ hab
          simp only [Bool.and_eq_true, beq_iff_eq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          obtain ⟨op, hop, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨cc, a, b, true, op, hC, hop, rfl, rfl, rfl⟩
        · cases h
  · cases h

theorem mmOp_nonShift {cc : IntCC} {sw : Bool} {op : BinaryOp} (h : mmOp cc sw = some op) :
    op.isShift = false := by
  cases cc <;> cases sw <;> simp only [mmOp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    rfl

theorem ruleSoundD_selMinMax {f : Function} {ty : Ty} {c x y : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), selMinMax tms ty c x y = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.select ty c x y), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.select ty c x y) := by
  intro tms x' h hord fr mem t ht hd
  obtain ⟨cc, a, b, sw, op, hC, hop, rfl, rfl, rfl⟩ := selMinMax_spec h
  obtain ⟨htc, hoc⟩ := nodeAt_spec hC
  obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.1 (hd c (by simp [operands]))
  have hc := hvc
  rw [tmVal_node htc hoc] at hc
  obtain ⟨A, B, hA, hB, rfl⟩ := (Opt.Proof.evalNode_icmp _ mem).1 hc
  have hc' : (tmFrame f tms fr mem).regs c = some ⟨.i8, Sem.icmp cc A B⟩ := hvc
  rw [tmVal_node' ht (hord t ht), evalNode_bin_of (mmOp_nonShift hop) hA hB]
  cases sw
  · simp only [Bool.false_eq_true, ite_false]
    rw [evalNode_select hA hB, hc']
    simp only [Option.map_some]
    rw [← sel_mm hop A B]
    rfl
  · simp only [ite_true]
    rw [evalNode_select hB hA, hc']
    simp only [Option.map_some]
    rw [← sel_mm hop A B]
    rfl

/-! ## `borMaskRe` -/

theorem borMaskRePlan_spec {tms : Array Tm} {ty : Ty} {a b x : Nat} {v : BitVec ty.width}
    (h : borMaskRePlan tms ty a b = some (x, v)) :
    ∃ a1 k1 k1v k2 y yv, nodeAt tms a = some (.binary .bor ty a1 k1) ∧
      constAt tms ty b = some k2 ∧ constAt tms ty k1 = some k1v ∧
      nodeAt tms a1 = some (.binary .band ty x y) ∧ constAt tms ty y = some yv ∧
      k1v ||| k2 = ~~~yv ∧ v = k1v ||| k2 := by
  unfold borMaskRePlan at h
  split at h
  · rename_i ty1 a1 k1 k2 hA hb
    split at h
    · rename_i hty1
      have hty1' : ty1 = ty := by simpa using hty1
      subst hty1'
      split at h
      · rename_i k1v ty2 x0 y hk1 hA1
        split at h
        · rename_i hty2
          have hty2' : ty2 = ty1 := by simpa using hty2
          subst hty2'
          split at h
          · rename_i yv hy
            split at h
            · rename_i hc
              cases h
              exact ⟨a1, k1, k1v, k2, y, yv, hA, hb, hk1, hA1, hy, by simpa using hc, rfl⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_borMaskRe {f : Function} {ty : Ty} {a b : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), borMaskRe tms ty a b = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        (∀ o ∈ operands (.binary .bor ty a b), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary .bor ty a b) := by
  intro tms x' h hord fr mem t ht hd
  unfold borMaskRe at h
  obtain ⟨⟨x, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  have hV : (tmFrame f tms fr mem).regs kc = some ⟨ty, v⟩ := tmVal_findConst hkc
  obtain ⟨a1, k1, k1v, k2, y, yv, hA, hb, hk1, hA1, hy, hyv, rfl⟩ := borMaskRePlan_spec hp
  obtain ⟨A1, K1, hA1v, hK1v, ha⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA (hd a (by simp [operands]))
  obtain ⟨X, Y, hX, hY, ha1⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hA1 (by rw [hA1v]; rfl)
  have hK1 : k1v = K1 := val_bits_eq ((constAt_spec hk1).symm.trans hK1v)
  have hYv : yv = Y := val_bits_eq ((constAt_spec hy).symm.trans hY)
  have hA1e : A1 = Sem.binary .band X Y := val_bits_eq (hA1v.symm.trans ha1)
  subst hK1
  subst hYv
  subst hA1e
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
  have ha' : (tmFrame f tms fr mem).regs a =
      some ⟨ty, Sem.binary .bor (Sem.binary .band X yv) k1v⟩ := ha
  have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, k2⟩ := constAt_spec hb
  rw [tmVal_node' ht (hord t ht), evalNode_bin_of rfl hX' hV, evalNode_bin_of rfl ha' hb']
  simp only [Sem.binary, Sem.band, Sem.bor, BitVec.or_assoc, hyv, or_and_not]

/-! ## `mulHi` -/

/-- The logical shift of a double-width value by its half width is its high half, zero-extended. -/
theorem ushr_half {h : Nat} (P : BitVec (h + h)) :
    P >>> h = BitVec.setWidth (h + h) (BitVec.extractLsb' h h P) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi,
    decide_true, Bool.true_and]
  by_cases hih : i < h
  · simp [hih]
  · simp [hih, BitVec.getLsbD_of_ge P (h + i) (by omega)]

/-- The arithmetic shift of a double-width value by its half width is its high half,
sign-extended. -/
theorem sshr_half {h : Nat} (hh : 0 < h) (P : BitVec (h + h)) :
    P.sshiftRight h = BitVec.signExtend (h + h) (BitVec.extractLsb' h h P) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend]
  have hm1 : (BitVec.extractLsb' h h P).msb = P.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb']
    have : h + (h - 1) = h + h - 1 := by omega
    simp [this, show h - 1 < h by omega]
  by_cases hih : i < h
  · simp [hi, hih, show h + i < h + h by omega, BitVec.getLsbD_extractLsb']
  · simp [hi, hih, show ¬ (h + i < h + h) by omega, hm1, show ¬ (h + h ≤ i) by omega]

theorem ushr_uext_mul {h W v : Nat} (hW : W = h + h) (hh : 0 < h) (X Y : BitVec h)
    (K : BitVec v) (hK : K.toNat = h) :
    Sem.ushr (Sem.uextend W X * Sem.uextend W Y) K = Sem.uextend W (Sem.umulhi X Y) := by
  subst hW
  have hs : Sem.shiftAmt (h + h) K = h := by
    simp only [Sem.shiftAmt, hK]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Sem.ushr, hs, Sem.umulhi, Sem.uextend]
  exact ushr_half _

theorem sshr_sext_mul {h W v : Nat} (hW : W = h + h) (hh : 0 < h) (X Y : BitVec h)
    (K : BitVec v) (hK : K.toNat = h) :
    Sem.sshr (Sem.sextend W X * Sem.sextend W Y) K = Sem.sextend W (Sem.smulhi X Y) := by
  subst hW
  have hs : Sem.shiftAmt (h + h) K = h := by
    simp only [Sem.shiftAmt, hK]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Sem.sshr, hs, Sem.smulhi, Sem.sextend]
  exact sshr_half hh _

theorem mulHiPlan_spec {aty : Tm → Option Ty} {tms : Array Tm} {op : BinaryOp} {ty : Ty}
    {m k : Nat} {hop : BinaryOp} {half : Ty} {x y : Nat}
    (h : mulHiPlan aty tms op ty m k = some (hop, half, x, y)) :
    ∃ eop e1 e2 K,
      ((op = .ushr ∧ eop = .uextend ∧ hop = .umulhi) ∨
        (op = .sshr ∧ eop = .sextend ∧ hop = .smulhi)) ∧
      nodeAt tms m = some (.binary .imul ty e1 e2) ∧ nodeAt tms e1 = some (.extend eop ty x) ∧
      nodeAt tms e2 = some (.extend eop ty y) ∧ constOf tms k = some K ∧
      tyAt aty tms x = some half ∧ tyAt aty tms y = some half ∧
      ty.width = half.width + half.width ∧ K.bits.toNat = half.width := by
  rw [mulHiPlan] at h
  obtain ⟨⟨eop, hop0⟩, hext, h2⟩ := Option.bind_eq_some_iff.1 h
  clear h
  have h := h2
  clear h2
  have hcase : (op = .ushr ∧ eop = .uextend ∧ hop0 = .umulhi) ∨
      (op = .sshr ∧ eop = .sextend ∧ hop0 = .smulhi) := by
    cases op <;> simp [mulHiOps] at hext <;> obtain ⟨rfl, rfl⟩ := hext <;> simp
  dsimp only at h
  split at h
  · rename_i ty' e1 e2 hM
    split at h
    · rename_i o1 t1 x0 o2 t2 y0 K hE1 hE2 hK
      split at h
      · rename_i hx hy htx hty
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hw⟩, hk⟩ := hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨_, e1, e2, K, hcase, hM, hE1, hE2, hK, htx, hty, hw, hk⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem ruleSoundD_mulHi {f : Function} {op : BinaryOp} {ty : Ty} {m k : Nat} :
    ∀ (tms : Array Tm) (x' : Tm), mulHi (atomTy f) tms op ty m k = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' →
        AtomsTyped f tms fr mem (.binary op ty m k) →
        (∀ o ∈ operands (.binary op ty m k), (tmVal f tms fr mem o).isSome) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty m k) := by
  intro tms x' h hord fr mem t ht hA hd
  unfold mulHi at h
  obtain ⟨⟨hop, half, x, y⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hn, hhn, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨eop, e1, e2, K, hcase, hM, hE1, hE2, hK, htx, hty, hw, hk⟩ := mulHiPlan_spec hp
  obtain ⟨htm, _⟩ := nodeAt_spec hM
  obtain ⟨hte1, _⟩ := nodeAt_spec hE1
  obtain ⟨hte2, _⟩ := nodeAt_spec hE2
  have hrm : TmReach tms (.binary op ty m k) m := .op (by simp [operands])
  have hrx : TmReach tms (.binary op ty m k) x :=
    .sub (.sub hrm htm (by simp [operands])) hte1 (by simp [operands])
  have hry : TmReach tms (.binary op ty m k) y :=
    .sub (.sub hrm htm (by simp [operands])) hte2 (by simp [operands])
  obtain ⟨E1, E2, hE1v, hE2v, hmv⟩ :=
    tmVal_bin_ops (f := f) (fr := fr) (mem := mem) rfl hM (hd m (by simp [operands]))
  obtain ⟨v1, hxv, _, he1⟩ :=
    tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE1 (by rw [hE1v]; rfl)
  obtain ⟨v2, hyv, _, he2⟩ :=
    tmVal_ext_ops (f := f) (fr := fr) (mem := mem) hE2 (by rw [hE2v]; rfl)
  obtain ⟨X, rfl⟩ := val_of_tyAt hA hrx htx hxv
  obtain ⟨Y, rfl⟩ := val_of_tyAt hA hry hty hyv
  have hE1e : E1 = extOp eop ty.width X := val_bits_eq (hE1v.symm.trans he1)
  have hE2e : E2 = extOp eop ty.width Y := val_bits_eq (hE2v.symm.trans he2)
  subst hE1e
  subst hE2e
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨half, X⟩ := hxv
  have hY' : (tmFrame f tms fr mem).regs y = some ⟨half, Y⟩ := hyv
  have hm' : (tmFrame f tms fr mem).regs m =
      some ⟨ty, Sem.binary .imul (extOp eop ty.width X) (extOp eop ty.width Y)⟩ := hmv
  have hK' : (tmFrame f tms fr mem).regs k = some K := tmVal_of_constOf hK
  have hhalf : 0 < half.width := Ty.width_pos _
  have hlt : half.width < ty.width := by omega
  obtain ⟨hf1, hf2⟩ := findTm_spec hhn
  have hop_ns : hop.isShift = false := by
    rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  have hhv : (tmFrame f tms fr mem).regs hn = some ⟨half, Sem.binary hop X Y⟩ := by
    show tmVal f tms fr mem hn = _
    rw [tmVal_node hf1 hf2, evalNode_bin_of hop_ns hX' hY']
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [tmVal_node' ht (hord t ht), evalNode_shift rfl, hm', hK']
    simp only [show (BinaryOp.umulhi == .umulhi) = true by decide, ite_true, evalNode_extend, hhv,
      Option.bind_some, hlt, Val.as?_mk, Sem.shift, Option.map_some, extOp, Sem.binary, Sem.imul]
    rw [ushr_uext_mul hw hhalf X Y K.bits hk]
  · rw [tmVal_node' ht (hord t ht), evalNode_shift rfl, hm', hK']
    simp only [show (BinaryOp.smulhi == .umulhi) = false by decide, Bool.false_eq_true, ite_false,
      evalNode_extend, hhv, Option.bind_some, hlt, ite_true, Val.as?_mk, Sem.shift,
      Option.map_some, extOp, Sem.binary, Sem.imul]
    rw [sshr_sext_mul hw hhalf X Y K.bits hk]

/-! ## Family 9 and the default normaliser -/

theorem ruleSoundD_fam9Step {f : Function} : RuleSoundD f (fam9Step (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA hd
  cases i with
  | binary op ty a b =>
    cases op
    case bor =>
      simp only [fam9Step] at h
      cases h1 : borMask tms ty a b with
      | some y =>
        rw [h1] at h
        cases h
        exact borMask_val h1 hord fr mem ht
      | none =>
        rw [h1] at h
        simp only [Option.orElse_none] at h
        exact ruleSoundD_borMaskRe tms x' h hord fr mem t ht hd
    case ushr => exact ruleSoundD_mulHi tms x' h hord fr mem t ht hA hd
    case sshr => exact ruleSoundD_mulHi tms x' h hord fr mem t ht hA hd
    all_goals simp [fam9Step] at h
  | unary op ty a =>
    cases op
    case bnot => exact ruleSoundD_notDec tms x' h hord fr mem t ht hd
    all_goals simp [fam9Step] at h
  | ireduce ty u =>
    simp only [fam9Step] at h
    cases h1 : redShl (atomTy f) tms ty u with
    | some y =>
      rw [h1] at h
      cases h
      exact ruleSoundD_redShl tms _ h1 hord fr mem t ht hA hd
    | none =>
      rw [h1] at h
      simp only [Option.orElse_none] at h
      exact ruleSoundD_redUn tms x' h hord fr mem t ht hA hd
  | extend op ty u => exact ruleSoundD_extExt tms x' h hord fr mem t ht hd
  | icmp cc ty a b =>
    simp only [fam9Step] at h
    cases h1 : shipCmp tms cc ty a b with
    | some y =>
      rw [h1] at h
      cases h
      exact ruleSoundD_shipCmp tms _ h1 hord fr mem t ht hd
    | none =>
      rw [h1] at h
      simp only [Option.orElse_none] at h
      exact ruleSoundD_extCmp tms x' h hord fr mem t ht hA hd
  | select ty c x y => exact ruleSoundD_selMinMax tms x' h hord fr mem t ht hd
  | _ => simp [fam9Step] at h

/-- **The validator's default normaliser is sound where the operands have values.** -/
theorem normSoundD_stdD {f : Function} : NormSoundD f (Norm.stdD f) :=
  normSoundD_orElse (normSoundD_guard ruleSoundD_fam8Step)
    (normSoundD_orElse (normSoundD_guard ruleSoundD_fam9Step)
      (normSoundD_orElse normSoundT_stdT.toD (normSoundD_guard ruleSoundD_dropStep)))

end Opt.MidVal

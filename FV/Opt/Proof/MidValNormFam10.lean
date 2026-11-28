import FV.Opt.Proof.MidValNormFam9

/-!
# Family 10: pairs of constants, doubled sums, zero offsets (#1119, agent MidendNext12)

`Norm.stdD f = Norm.orElse (Norm.guard fam8Step) (Norm.orElse (Norm.guard (fam9Step (atomTy f)))
(Norm.orElse (Norm.guard (fam10Step (atomTy f))) (Norm.orElse (Norm.stdT f) (Norm.guard (dropStep
(atomTy f))))))` (`FV/Opt/MidVal.lean`), the validator's default normaliser. Each rule of
`fam10Step` gives a node with the value of the node it rewrites wherever the node's operands have
values and the atoms below it are typed (`RuleSoundD`, `FV/Opt/Proof/MidValNormDrop.lean`), proved
against `Clif.evalInst`:

* `pairRe` — `(x op k1) op (y op k2) = (x op y) op (k1 op k2)` for `iadd`, `imul`, `band`, `bor`,
  `bxor` (`pairOp_spec`, `swap_mid`), and `x op y` itself when `k1 op k2` is neutral
  (`rNeutral_spec`);
* `dblRe` — `a * 2`, `2 * a` and `a << 1` are `a + a` (`dblOf_spec`), then `pairRe`;
* `idNode` — `a op k = a` for a neutral `k` and a node `a` whose result type is the node's type
  (`Opt.evalInst_types`);
* `affZero` — `y + 0 = y` for the affine form `(y, 0)` of the node (`affPlan_spec`), `y` of its
  static type (`tyAt_val`, reached from the node: `affPlan_reach`).

Main results: `ruleSoundD_fam10Step`, **`normSoundD_stdD : NormSoundD f (Norm.stdD f)`** (moved
here from `MidValNormFam9.lean`, statement unchanged).
-/

namespace Opt.MidVal

open Clif

/-! ## `pairRe` -/

/-- `(a op b) op (c op d) = (a op c) op (b op d)` for an associative, commutative `op`. -/
theorem swap_mid {α : Type} (op : α → α → α) (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (comm : ∀ a b, op a b = op b a) (a b c d : α) :
    op (op a b) (op c d) = op (op a c) (op b d) := by
  rw [assoc, ← assoc b, comm b c, assoc, ← assoc]

theorem pairOp_spec {w : Nat} {op : BinaryOp} {k1 k2 K : BitVec w} (h : pairOp op k1 k2 = some K) :
    op.isShift = false ∧ ∀ X Y : BitVec w,
      Sem.binary op (Sem.binary op X k1) (Sem.binary op Y k2) =
        Sem.binary op (Sem.binary op X Y) K := by
  cases op <;> simp [pairOp, reOp] at h <;> subst h <;> refine ⟨rfl, fun X Y => ?_⟩ <;>
    simp only [Sem.binary, Sem.iadd, Sem.imul, Sem.band, Sem.bor, Sem.bxor]
  all_goals first
    | exact swap_mid (· + ·) BitVec.add_assoc BitVec.add_comm X k1 Y k2
    | exact swap_mid (· * ·) BitVec.mul_assoc BitVec.mul_comm X k1 Y k2
    | exact swap_mid (· &&& ·) BitVec.and_assoc BitVec.and_comm X k1 Y k2
    | exact swap_mid (· ||| ·) BitVec.or_assoc BitVec.or_comm X k1 Y k2
    | exact swap_mid (· ^^^ ·) BitVec.xor_assoc BitVec.xor_comm X k1 Y k2

theorem pairPlan_spec {tms : Array Tm} {op : BinaryOp} {ty : Ty} {a b x y : Nat}
    {K : BitVec ty.width} (h : pairPlan tms op ty a b = some (x, y, K)) :
    ∃ k1 k2 v1 v2, nodeAt tms a = some (.binary op ty x k1) ∧
      nodeAt tms b = some (.binary op ty y k2) ∧ constAt tms ty k1 = some v1 ∧
      constAt tms ty k2 = some v2 ∧ pairOp op v1 v2 = some K := by
  unfold pairPlan at h
  split at h
  · rename_i op1 t1 x0 k1 op2 t2 y0 k2 hA hB
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hc
      split at h
      · rename_i v1 v2 h1 h2
        obtain ⟨K', hK, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨k1, k2, v1, v2, hA, hB, h1, h2, hK⟩
      · cases h
    · cases h
  · cases h

/-- `pairRe`'s term has the node's value where both operands have values. -/
theorem pairRe_val {f : Function} {tms : Array Tm} {op : BinaryOp} {ty : Ty} {a b : Nat}
    {x' : Tm} (h : pairRe tms op ty a b = some x')
    (hord : ∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) {fr : Frame} {mem : Mem} {t : Nat}
    (ht : tms[t]? = some x') (hda : (tmVal f tms fr mem a).isSome)
    (hdb : (tmVal f tms fr mem b).isSome) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) := by
  unfold pairRe at h
  obtain ⟨⟨x, y, K⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k1, k2, v1, v2, hA, hB, h1, h2, hK⟩ := pairPlan_spec hp
  obtain ⟨hns, hsem⟩ := pairOp_spec hK
  obtain ⟨X, K1, hX, hK1, ha⟩ := tmVal_bin_ops (f := f) (fr := fr) (mem := mem) hns hA hda
  obtain ⟨Y, K2, hY, hK2, hb⟩ := tmVal_bin_ops (f := f) (fr := fr) (mem := mem) hns hB hdb
  have e1 : v1 = K1 := val_bits_eq ((constAt_spec h1).symm.trans hK1)
  have e2 : v2 = K2 := val_bits_eq ((constAt_spec h2).symm.trans hK2)
  subst e1
  subst e2
  have hX' : (tmFrame f tms fr mem).regs x = some ⟨ty, X⟩ := hX
  have hY' : (tmFrame f tms fr mem).regs y = some ⟨ty, Y⟩ := hY
  have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, Sem.binary op X v1⟩ := ha
  have hb' : (tmFrame f tms fr mem).regs b = some ⟨ty, Sem.binary op Y v2⟩ := hb
  obtain ⟨hm1, hm2⟩ := findTm_spec hm
  have hmv : (tmFrame f tms fr mem).regs m = some ⟨ty, Sem.binary op X Y⟩ := by
    show tmVal f tms fr mem m = _
    rw [tmVal_node hm1 hm2, evalNode_bin_of hns hX' hY']
  rw [evalNode_bin_of hns ha' hb', hsem X Y]
  split at h
  · rename_i hn
    have hx' : x' = .node (.binary op ty x y) := by
      rw [hm1] at h
      exact (Option.some.inj h).symm
    subst hx'
    rw [tmVal_same ht hm1 (hord t ht) hm2, rNeutral_spec hn]
    exact hmv
  · split at h
    · cases h
    · obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
      have hV : (tmFrame f tms fr mem).regs kc = some ⟨ty, K⟩ := tmVal_findConst hkc
      rw [tmVal_node' ht (hord t ht), evalNode_bin_of hns hmv hV]

/-! ## `dblRe` -/

/-- `dblOf`'s `d`: an operand, and the node is `iadd ty d d`. -/
theorem dblOf_spec {f : Function} {tms : Array Tm} {op : BinaryOp} {ty : Ty} {a b d : Nat}
    (h : dblOf tms op ty a b = some d) (fr : Frame) (mem : Mem) :
    (d = a ∨ d = b) ∧ evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) =
      evalNode (tmFrame f tms fr mem) mem (.binary .iadd ty d d) := by
  cases op
  case imul =>
    simp only [dblOf] at h
    split at h
    · rename_i h2
      simp only [Option.some.injEq] at h
      subst h
      have hc : (tmFrame f tms fr mem).regs b = some ⟨ty, 2⟩ := constAt_spec (by simpa using h2)
      refine ⟨Or.inl rfl, ?_⟩
      rw [evalNode_binary_nonShift rfl, evalNode_binary_nonShift rfl, hc]
      rcases (tmFrame f tms fr mem).regs a |>.bind (·.as? ty) with _ | A
      · rfl
      · simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.binary, Sem.iadd, Sem.imul]
        rw [(add_self_eq_mul_two A).1]
    · split at h
      · rename_i _ h2
        simp only [Option.some.injEq] at h
        subst h
        have hc : (tmFrame f tms fr mem).regs a = some ⟨ty, 2⟩ := constAt_spec (by simpa using h2)
        refine ⟨Or.inr rfl, ?_⟩
        rw [evalNode_binary_nonShift rfl, evalNode_binary_nonShift rfl, hc]
        rcases hB : (tmFrame f tms fr mem).regs b |>.bind (·.as? ty) with _ | B
        · simp [hB]
        · simp only [Option.bind_some, Val.as?_mk, Option.map_some, Sem.binary, Sem.iadd,
            Sem.imul, hB]
          rw [(add_self_eq_mul_two B).2]
      · cases h
  case ishl =>
    simp only [dblOf] at h
    split at h
    · rename_i K hK
      split at h
      · rename_i h1
        simp only [beq_iff_eq] at h1
        simp only [Option.some.injEq] at h
        subst h
        have hKv : (tmFrame f tms fr mem).regs b = some K := tmVal_of_constOf hK
        refine ⟨Or.inl rfl, ?_⟩
        rw [evalNode_ishl hKv, evalNode_binary_nonShift rfl]
        rcases (tmFrame f tms fr mem).regs a |>.bind (·.as? ty) with _ | A
        · rfl
        · simp only [Option.bind_some, Option.map_some, Val.as?_mk, Sem.binary, Sem.iadd,
            Sem.ishl, Sem.shiftAmt, h1, shl_one]
      · cases h
    · cases h
  all_goals simp [dblOf] at h

/-! ## `idNode` -/

/-- A value whose type is `ty`. -/
theorem val_of_ty {v : Val} {ty : Ty} (h : v.ty = ty) : ∃ X : BitVec ty.width, v = ⟨ty, X⟩ := by
  obtain ⟨vt, X⟩ := v
  simp only at h
  subst h
  exact ⟨X, rfl⟩

/-- `idNode`'s term has the node's value where its first operand has a value. -/
theorem idNode_val {f : Function} {tms : Array Tm} {op : BinaryOp} {ty : Ty} {a b : Nat}
    {x' : Tm} (h : idNode tms op ty a b = some x')
    (hord : ∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) {fr : Frame} {mem : Mem} {t : Nat}
    (ht : tms[t]? = some x') (hda : (tmVal f tms fr mem a).isSome) :
    tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) := by
  unfold idNode at h
  split at h
  · rename_i j kv hj hkv
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hn, hrt⟩ := hc
      obtain ⟨htj, hoj⟩ := nodeAt_spec hj
      have hx' : x' = .node j := by
        rw [htj] at h
        exact (Option.some.inj h).symm
      subst hx'
      rw [tmVal_same ht htj (hord t ht) hoj]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hda
      have hvt : v.ty = ty := by
        have he := hv
        rw [tmVal_node htj hoj] at he
        obtain ⟨m', hm'⟩ := evalNode_some_iff.1 he
        simpa using evalInst_types hm' hrt
      obtain ⟨V, rfl⟩ := val_of_ty hvt
      have hk : (tmFrame f tms fr mem).regs b = some ⟨ty, kv⟩ := constAt_spec hkv
      have ha' : (tmFrame f tms fr mem).regs a = some ⟨ty, V⟩ := hv
      rw [hv, evalNode_bin_of (rNeutral_nonShift hn) ha' hk, rNeutral_spec hn]
    · cases h
  · cases h

/-! ## `affZero` -/

/-- `affPlan`'s term `y` is reached from the node's operands. -/
theorem affPlan_reach {tms : Array Tm} {i : Inst} {y : Nat} {K : Val}
    (h : affPlan tms i = some (y, K)) : TmReach tms i y := by
  cases i with
  | binary op ty a b =>
    cases op
    case iadd =>
      simp only [affPlan] at h
      cases hb : constAt tms ty b with
      | some kb =>
        simp only [hb] at h
        obtain ⟨k1, v, hn, _, _⟩ := foldAdd_spec h
        exact .sub (.op (by simp [operands])) (nodeAt_spec hn).1 (by simp [operands])
      | none =>
        cases ha : constAt tms ty a with
        | some ka =>
          simp only [hb, ha] at h
          obtain ⟨k1, v, hn, _, _⟩ := foldAdd_spec h
          exact .sub (.op (by simp [operands])) (nodeAt_spec hn).1 (by simp [operands])
        | none => simp [hb, ha] at h
    case isub =>
      simp only [affPlan] at h
      cases hb : constAt tms ty b with
      | some kb =>
        simp only [hb] at h
        cases hf : foldAdd tms ty a (-kb) with
        | some p =>
          rw [hf] at h
          simp only [Option.orElse_some] at h
          cases h
          obtain ⟨k1, v, hn, _, _⟩ := foldAdd_spec hf
          exact .sub (.op (by simp [operands])) (nodeAt_spec hn).1 (by simp [operands])
        | none =>
          rw [hf] at h
          simp only [Option.orElse_none, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .op (by simp [operands])
      | none => simp [hb] at h
    all_goals simp [affPlan] at h
  | _ => simp [affPlan] at h

theorem ruleSoundD_affZero {f : Function} {i : Inst} :
    ∀ (tms : Array Tm) (x' : Tm), affZero (atomTy f) tms i = some x' →
      (∀ t, tms[t]? = some x' → ∀ o ∈ x'.ops, o < t) →
      ∀ (fr : Frame) (mem : Mem) (t : Nat), tms[t]? = some x' → AtomsTyped f tms fr mem i →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem i := by
  intro tms x' h hord fr mem t ht hA
  unfold affZero at h
  obtain ⟨⟨y, K⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  split at h
  · rename_i hc
    obtain ⟨h0, hty⟩ := hc
    rw [tmVal_same ht h (hord t ht) (tyAt_ops hty h), affPlan_spec hp f fr mem, h0]
    have hr : (tmFrame f tms fr mem).regs y = tmVal f tms fr mem y := rfl
    rw [hr]
    rcases hv : tmVal f tms fr mem y with _ | v
    · rfl
    · obtain ⟨V, rfl⟩ := val_of_ty (tyAt_val hA (affPlan_reach hp) hty hv)
      simp
  · cases h

/-! ## Family 10 and the default normaliser -/

theorem ruleSoundD_fam10Step {f : Function} : RuleSoundD f (fam10Step (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA hd
  cases i with
  | binary op ty a b =>
    have hda : (tmVal f tms fr mem a).isSome := hd a (by simp [operands])
    have hdb : (tmVal f tms fr mem b).isSome := hd b (by simp [operands])
    simp only [fam10Step] at h
    cases h1 : pairRe tms op ty a b with
    | some y =>
      rw [h1] at h
      cases h
      exact pairRe_val h1 hord ht hda hdb
    | none =>
      rw [h1] at h
      simp only [Option.orElse_none] at h
      cases h2 : dblRe tms op ty a b with
      | some y =>
        rw [h2] at h
        cases h
        unfold dblRe at h2
        obtain ⟨d, hdd, hp⟩ := Option.bind_eq_some_iff.1 h2
        obtain ⟨hor, heq⟩ := dblOf_spec (f := f) hdd fr mem
        have hdd' : (tmVal f tms fr mem d).isSome := by
          rcases hor with rfl | rfl
          · exact hda
          · exact hdb
        rw [heq]
        exact pairRe_val hp hord ht hdd' hdd'
      | none =>
        rw [h2] at h
        simp only [Option.orElse_none] at h
        cases h3 : idNode tms op ty a b with
        | some y =>
          rw [h3] at h
          cases h
          exact idNode_val h3 hord ht hda
        | none =>
          rw [h3] at h
          simp only [Option.orElse_none] at h
          exact ruleSoundD_affZero tms x' h hord fr mem t ht hA
  | _ => simp [fam10Step] at h

/-- **The validator's default normaliser is sound where the operands have values.** -/
theorem normSoundD_stdD {f : Function} : NormSoundD f (Norm.stdD f) :=
  normSoundD_orElse (normSoundD_guard ruleSoundD_fam8Step)
    (normSoundD_orElse (normSoundD_guard ruleSoundD_fam9Step)
      (normSoundD_orElse (normSoundD_guard ruleSoundD_fam10Step)
        (normSoundD_orElse normSoundT_stdT.toD (normSoundD_guard ruleSoundD_dropStep))))

end Opt.MidVal

import FV.Opt.Proof.MidValNormTyped

/-!
# Family 4 is a sound normaliser under typing (#1119 stage 2, agent MidendNorm5)

`Norm.stdT f = Norm.narrowN f 3` (`FV/Opt/MidVal.lean`): `Norm.std`, the typed rules, then four
steps, each proved here against `Clif.evalInst`:

* `idStep` (typed) — `op ty x k` with `k` a neutral constant of type `ty` (`x+0`, `x-0`, `x*1`,
  `x|0`, `x^0`, `x&-1`), or `op ty k x` with `op` commutative, is `x` when `x` has static type
  `ty` (`tyAt`): with `x` of type `ty` the operation gives `x`'s bits (`rNeutral_spec`,
  `commOp_spec`); with no value for `x` neither side has one. Without the typing the rewrite is
  false (`FVTest/Opt/MidValFam4Witness.lean`: an operand of another width is `stuck` in the
  operation, not as itself);
* `affStep` — `iadd ty x k`, `iadd ty k x` (`x` an `iadd` with a constant) and `isub ty x k` are
  `iadd ty y K` with the constants added up (`affPlan_spec`: associativity and commutativity of
  `+` modulo `2^width`, `x - k = x + (-k)`); no typing: both sides read `y` at type `ty`;
* `swapStep` — `op ty k x` is `op ty x k` for a commutative `op` (`commOp_spec`; both sides read
  both operands at type `ty`);
* `narrowStep n` (typed, for a normaliser `n` sound under typing) — `ireduce ty (op wty a b)` with
  `op` a ring operation and `a`, `b` of static type `wty` wider than `ty` is `op ty a' b'` with
  `a'`, `b'` the terms of `ireduce ty a`, `ireduce ty b` under `n` (`redOf_spec`): truncation
  commutes with `+`, `-`, `*`, `&`, `|`, `^` (`setWidth_ring`); then `affStep`/`swapStep` on that
  node.

Main results: `ruleSoundT_idStep`, `ruleSound_affStep`, `ruleSound_swapStep`,
`ruleSoundT_narrowStep`. `normSoundT_base`, `normSoundT_narrowN` and `normSoundT_stdT` (the
validator's default normaliser, which now ends with family 5) are in
`FV/Opt/Proof/MidValNormFam5.lean`.
-/

namespace Opt.MidVal

open Clif

/-! ## Common facts -/

/-- Two slots holding the same term, whose operands are earlier than both, have one value. -/
theorem tmVal_same {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {t s : Nat} {x : Tm}
    (ht : tms[t]? = some x) (hs : tms[s]? = some x) (hot : ∀ o ∈ x.ops, o < t)
    (hos : ∀ o ∈ x.ops, o < s) : tmVal f tms fr mem t = tmVal f tms fr mem s := by
  cases x with
  | node j => rw [tmVal_node' ht hot, tmVal_node' hs hos]
  | param b i => rw [tmVal_atom ht (fun _ h => by cases h), tmVal_atom hs (fun _ h => by cases h)]
  | res b k j => rw [tmVal_atom ht (fun _ h => by cases h), tmVal_atom hs (fun _ h => by cases h)]
  | poison b k => rw [tmVal_atom ht (fun _ h => by cases h), tmVal_atom hs (fun _ h => by cases h)]

/-- A term with a static type has its operands earlier. -/
theorem tyAt_ops {aty : Tm → Option Ty} {tms : Array Tm} {x : Nat} {ty : Ty} {a : Tm}
    (h : tyAt aty tms x = some ty) (hx : tms[x]? = some a) : ∀ o ∈ a.ops, o < x := by
  unfold tyAt at h
  rw [hx] at h
  cases a with
  | node j =>
    simp only at h
    split at h
    · rename_i ho
      simpa [Tm.ops, List.all_eq_true] using ho
    · cases h
  | _ => intro o ho; simp [Tm.ops] at ho

theorem rNeutral_spec {w : Nat} {op : BinaryOp} {k : BitVec w} (h : rNeutral op k = true)
    (x : BitVec w) : Sem.binary op x k = x := by
  cases op <;> simp only [rNeutral, beq_iff_eq, Bool.false_eq_true] at h <;> subst h <;>
    simp [Sem.binary, Sem.iadd, Sem.isub, Sem.imul, Sem.band, Sem.bor, Sem.bxor]

theorem rNeutral_nonShift {w : Nat} {op : BinaryOp} {k : BitVec w} (h : rNeutral op k = true) :
    op.isShift = false := by
  cases op <;> simp_all [rNeutral, BinaryOp.isShift]

theorem umin_comm {w : Nat} (x y : BitVec w) : Sem.umin x y = Sem.umin y x := by
  unfold Sem.umin
  by_cases h1 : x.ule y <;> by_cases h2 : y.ule x <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.ule, decide_eq_true_eq] at h1 h2; omega)

theorem umax_comm {w : Nat} (x y : BitVec w) : Sem.umax x y = Sem.umax y x := by
  unfold Sem.umax
  by_cases h1 : x.ule y <;> by_cases h2 : y.ule x <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.ule, decide_eq_true_eq] at h1 h2; omega)

theorem smin_comm {w : Nat} (x y : BitVec w) : Sem.smin x y = Sem.smin y x := by
  unfold Sem.smin
  by_cases h1 : x.sle y <;> by_cases h2 : y.sle x <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toInt_eq; simp only [BitVec.sle, decide_eq_true_eq] at h1 h2; omega)

theorem smax_comm {w : Nat} (x y : BitVec w) : Sem.smax x y = Sem.smax y x := by
  unfold Sem.smax
  by_cases h1 : x.sle y <;> by_cases h2 : y.sle x <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true]
  all_goals first
    | rfl
    | (apply BitVec.eq_of_toInt_eq; simp only [BitVec.sle, decide_eq_true_eq] at h1 h2; omega)

theorem commOp_spec {w : Nat} {op : BinaryOp} (h : commOp op = true) (x y : BitVec w) :
    Sem.binary op x y = Sem.binary op y x := by
  cases op <;> simp only [commOp, Bool.false_eq_true] at h <;> simp only [Sem.binary]
  · exact BitVec.add_comm x y
  · exact BitVec.mul_comm x y
  · exact BitVec.and_comm x y
  · exact BitVec.or_comm x y
  · exact BitVec.xor_comm x y
  · exact smin_comm x y
  · exact smax_comm x y
  · exact umin_comm x y
  · exact umax_comm x y

theorem commOp_nonShift {op : BinaryOp} (h : commOp op = true) : op.isShift = false := by
  cases op <;> simp_all [commOp, BinaryOp.isShift]

theorem ringOp_nonShift {op : BinaryOp} (h : ringOp op = true) : op.isShift = false := by
  cases op <;> simp_all [ringOp, BinaryOp.isShift]

theorem setWidth_sub' {w m : Nat} (x y : BitVec w) (hm : m ≤ w) :
    (x - y).setWidth m = x.setWidth m - y.setWidth m := by
  have h := BitVec.setWidth_add (x - y) y hm
  rw [BitVec.sub_add_cancel] at h
  rw [h, BitVec.add_sub_cancel]

/-- Truncation commutes with the ring operations. -/
theorem setWidth_ring {w m : Nat} {op : BinaryOp} (hop : ringOp op = true) (hm : m ≤ w)
    (A B : BitVec w) :
    BitVec.setWidth m (Sem.binary op A B) =
      Sem.binary op (BitVec.setWidth m A) (BitVec.setWidth m B) := by
  cases op <;> simp only [ringOp, Bool.false_eq_true] at hop <;>
    simp only [Sem.binary, Sem.iadd, Sem.isub, Sem.imul, Sem.band, Sem.bor, Sem.bxor]
  · exact BitVec.setWidth_add A B hm
  · exact setWidth_sub' A B hm
  · exact BitVec.setWidth_mul A B hm
  · exact BitVec.setWidth_and
  · exact BitVec.setWidth_or
  · exact BitVec.setWidth_xor

/-- A value read at its own type. -/
theorem bind_as_map {ty : Ty} (X : Option (BitVec ty.width)) (g : BitVec ty.width → BitVec ty.width) :
    ((X.map fun B => (⟨ty, g B⟩ : Val)).bind (·.as? ty)) = X.map g := by
  cases X <;> simp

/-! ## `idStep` -/

theorem idPick_spec {aty : Tm → Option Ty} {tms : Array Tm} {op : BinaryOp} {ty : Ty} {x k : Nat}
    {x' : Tm} (h : idPick aty tms op ty x k = some x') :
    ∃ kv, constAt tms ty k = some kv ∧ rNeutral op kv = true ∧ tyAt aty tms x = some ty ∧
      tms[x]? = some x' := by
  unfold idPick at h
  split at h
  · rename_i kv hkv
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨kv, hkv, hc.1, hc.2, h⟩
    · cases h
  · cases h

theorem ruleSoundT_idStep {f : Function} : RuleSoundT f (idStep (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  cases i with
  | binary op ty a b =>
    simp only [idStep, idTyped] at h
    -- the operand `x` that is the result, the constant `k`, and which side `k` is on
    have key : ∀ (x k : Nat) (kv : BitVec ty.width), tyAt (atomTy f) tms x = some ty →
        tms[x]? = some x' → constAt tms ty k = some kv → rNeutral op kv = true →
        TmReach tms (.binary op ty a b) x →
        (∀ A, ((tmFrame f tms fr mem).regs x).bind (·.as? ty) = some A →
          evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) = some ⟨ty, A⟩) →
        (((tmFrame f tms fr mem).regs x) = none →
          evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) = none) →
        tmVal f tms fr mem t = evalNode (tmFrame f tms fr mem) mem (.binary op ty a b) := by
      intro x k kv htx hx _ _ hr hsome hnone
      rw [tmVal_same ht hx (hord t ht) (tyAt_ops htx hx)]
      rcases hv : tmVal f tms fr mem x with _ | v
      · exact (hnone hv).symm
      · have hvt : v.ty = ty := tyAt_val hA hr htx hv
        obtain ⟨vt, vb⟩ := v
        simp only at hvt
        subst hvt
        refine (hsome vb ?_).symm
        show (tmVal f tms fr mem x).bind _ = _
        rw [hv]
        simp
    cases h1 : idPick (atomTy f) tms op ty a b with
    | some y =>
      rw [h1] at h
      cases h
      obtain ⟨kv, hkv, hn, htx, hx⟩ := idPick_spec h1
      have hop := rNeutral_nonShift hn
      have hk : (tmFrame f tms fr mem).regs b = some ⟨ty, kv⟩ := constAt_spec hkv
      refine key a b kv htx hx hkv hn (.op (by simp [operands])) ?_ ?_
      · intro A hA'
        rw [evalNode_binary_nonShift hop, hA', hk]
        simp [rNeutral_spec hn]
      · intro hnone
        rw [evalNode_binary_nonShift hop, hnone]
        rfl
    | none =>
      rw [h1] at h
      simp only [Option.orElse_none] at h
      split at h
      · rename_i hc
        obtain ⟨kv, hkv, hn, htx, hx⟩ := idPick_spec h
        have hop := commOp_nonShift hc
        have hk : (tmFrame f tms fr mem).regs a = some ⟨ty, kv⟩ := constAt_spec hkv
        refine key b a kv htx hx hkv hn (.op (by simp [operands])) ?_ ?_
        · intro A hA'
          rw [evalNode_binary_nonShift hop, hA', hk]
          simp [commOp_spec hc kv A, rNeutral_spec hn]
        · intro hnone
          rw [evalNode_binary_nonShift hop, hnone, hk]
          simp
      · cases h
  | _ => simp [idStep] at h

/-! ## `affStep` -/

theorem evalNode_addK {F : Frame} {mem : Mem} {ty : Ty} {x c : ValueId} {kv : BitVec ty.width}
    (hc : F.regs c = some ⟨ty, kv⟩) :
    evalNode F mem (.binary .iadd ty x c) = ((F.regs x).bind (·.as? ty)).map fun A => ⟨ty, A + kv⟩ := by
  rw [evalNode_binary_nonShift rfl, hc]
  rcases (F.regs x).bind (·.as? ty) with _ | A <;> simp [Sem.binary, Sem.iadd]

theorem evalNode_kAdd {F : Frame} {mem : Mem} {ty : Ty} {x c : ValueId} {kv : BitVec ty.width}
    (hc : F.regs c = some ⟨ty, kv⟩) :
    evalNode F mem (.binary .iadd ty c x) = ((F.regs x).bind (·.as? ty)).map fun A => ⟨ty, kv + A⟩ := by
  rw [evalNode_binary_nonShift rfl, hc]
  rcases (F.regs x).bind (·.as? ty) with _ | A <;> simp [Sem.binary, Sem.iadd]

theorem evalNode_subK {F : Frame} {mem : Mem} {ty : Ty} {x c : ValueId} {kv : BitVec ty.width}
    (hc : F.regs c = some ⟨ty, kv⟩) :
    evalNode F mem (.binary .isub ty x c) = ((F.regs x).bind (·.as? ty)).map fun A => ⟨ty, A - kv⟩ := by
  rw [evalNode_binary_nonShift rfl, hc]
  rcases (F.regs x).bind (·.as? ty) with _ | A <;> simp [Sem.binary, Sem.isub]

theorem foldAdd_spec {tms : Array Tm} {ty : Ty} {x : Nat} {k : BitVec ty.width} {y : Nat} {K : Val}
    (h : foldAdd tms ty x k = some (y, K)) :
    ∃ k1 v, nodeAt tms x = some (.binary .iadd ty y k1) ∧ constAt tms ty k1 = some v ∧
      K = ⟨ty, v + k⟩ := by
  unfold foldAdd at h
  split at h
  · rename_i ty' y' k1 hn
    split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      subst he
      obtain ⟨v, hv, he2⟩ := Option.map_eq_some_iff.1 h
      cases he2
      exact ⟨k1, v, hn, hv, rfl⟩
    · cases h
  · cases h

/-- The value of `x = iadd ty y k1` read at `ty`. -/
theorem regs_addK {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {x y k1 : Nat} {ty : Ty}
    {v : BitVec ty.width} (hn : nodeAt tms x = some (.binary .iadd ty y k1))
    (hv : constAt tms ty k1 = some v) :
    ((tmFrame f tms fr mem).regs x).bind (·.as? ty) =
      (((tmFrame f tms fr mem).regs y).bind (·.as? ty)).map fun B => B + v := by
  have : (tmFrame f tms fr mem).regs x = (((tmFrame f tms fr mem).regs y).bind (·.as? ty)).map
      fun B => ⟨ty, B + v⟩ := by
    show tmVal f tms fr mem x = _
    rw [tmVal_node (nodeAt_spec hn).1 (nodeAt_spec hn).2]
    exact evalNode_addK (constAt_spec hv)
  rw [this, bind_as_map]

theorem affPlan_spec {tms : Array Tm} {i : Inst} {y : Nat} {K : Val}
    (h : affPlan tms i = some (y, K)) (f : Function) (fr : Frame) (mem : Mem) :
    evalNode (tmFrame f tms fr mem) mem i =
      (((tmFrame f tms fr mem).regs y).bind (·.as? K.ty)).map fun B => ⟨K.ty, B + K.bits⟩ := by
  cases i with
  | binary op ty a b =>
    cases op
    case iadd =>
      simp only [affPlan] at h
      cases hb : constAt tms ty b with
      | some kb =>
        simp only [hb] at h
        obtain ⟨k1, v, hn, hv, rfl⟩ := foldAdd_spec h
        rw [evalNode_addK (constAt_spec hb), regs_addK hn hv]
        rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty) with _ | B <;>
          simp [BitVec.add_assoc]
      | none =>
        cases ha : constAt tms ty a with
        | some ka =>
          simp only [hb, ha] at h
          obtain ⟨k1, v, hn, hv, rfl⟩ := foldAdd_spec h
          rw [evalNode_kAdd (constAt_spec ha), regs_addK hn hv]
          rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty) with _ | B <;>
            simp only [Option.map_none, Option.map_some]
          congr 2
          rw [BitVec.add_comm ka, BitVec.add_assoc]
        | none => simp [hb, ha] at h
    case isub =>
      simp only [affPlan] at h
      cases hb : constAt tms ty b with
      | some kb =>
        simp only [hb] at h
        rw [evalNode_subK (constAt_spec hb)]
        cases hf : foldAdd tms ty a (-kb) with
        | some p =>
          rw [hf] at h
          simp only [Option.orElse_some] at h
          cases h
          obtain ⟨k1, v, hn, hv, rfl⟩ := foldAdd_spec hf
          rw [regs_addK hn hv]
          rcases ((tmFrame f tms fr mem).regs y).bind (·.as? ty) with _ | B <;>
            simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        | none =>
          rw [hf] at h
          simp only [Option.orElse_none, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases ((tmFrame f tms fr mem).regs a).bind (·.as? ty) with _ | B <;>
            simp [BitVec.sub_eq_add_neg]
      | none => simp [hb] at h
    all_goals simp [affPlan] at h
  | _ => simp [affPlan] at h

theorem ruleSound_affStep : RuleSound affStep := by
  intro tms i x' h hord f fr mem t ht
  unfold affStep at h
  obtain ⟨⟨y, K⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨kc, hkc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hk1, hk2⟩ := findTm_spec hkc
  have hK : (tmFrame f tms fr mem).regs kc = some ⟨K.ty, K.bits⟩ := by
    show tmVal f tms fr mem kc = _
    rw [tmVal_node hk1 hk2]
    rfl
  rw [tmVal_node ht (hord t ht), evalNode_addK hK, affPlan_spec hp]

/-! ## `swapStep` -/

theorem ruleSound_swapStep : RuleSound swapStep := by
  intro tms i x' h hord f fr mem t ht
  cases i with
  | binary op ty a b =>
    simp only [swapStep] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      have hcomm := hc.1.1
      have hop := commOp_nonShift hcomm
      rw [tmVal_node ht (hord t ht), evalNode_binary_nonShift hop, evalNode_binary_nonShift hop]
      rcases ((tmFrame f tms fr mem).regs a).bind (·.as? ty) with _ | A <;>
        rcases ((tmFrame f tms fr mem).regs b).bind (·.as? ty) with _ | B <;>
        simp only [Option.bind_none, Option.bind_some, Option.map_none, Option.map_some]
      rw [commOp_spec hcomm B A]
    · cases h
  | _ => simp [swapStep] at h

/-! ## `narrowStep` -/

theorem TmReach.of_ops {tms : Array Tm} {i i' : Inst}
    (h : ∀ o ∈ operands i', TmReach tms i o) {u : Nat} (hr : TmReach tms i' u) :
    TmReach tms i u := by
  induction hr with
  | op ho => exact h _ ho
  | sub _ hw hu ih => exact .sub ih hw hu

theorem AtomsTyped.of_ops {f : Function} {tms : Array Tm} {fr : Frame} {mem : Mem} {i i' : Inst}
    (hA : AtomsTyped f tms fr mem i) (h : ∀ o ∈ operands i', TmReach tms i o) :
    AtomsTyped f tms fr mem i' :=
  fun u a ty v hr => hA u a ty v (TmReach.of_ops h hr)

/-- The term `redOf` gives has the value of `ireduce ty a`. -/
theorem redOf_spec {f : Function} {n : Norm} (hn : NormSoundT f n) {tms : Array Tm} {ty : Ty}
    {a a' : Nat} (h : redOf n tms ty a = some a') {fr : Frame} {mem : Mem}
    (hA : AtomsTyped f tms fr mem (.ireduce ty a)) :
    tmVal f tms fr mem a' = evalNode (tmFrame f tms fr mem) mem (.ireduce ty a) := by
  unfold redOf at h
  cases hx : n tms (.ireduce ty a) with
  | some x =>
    rw [hx, Option.getD_some] at h
    exact hn tms _ x hx fr mem a' (findTm_spec h).1 hA
  | none =>
    rw [hx, Option.getD_none] at h
    obtain ⟨h1, h2⟩ := findTm_spec h
    exact tmVal_node h1 h2

theorem ruleSoundT_narrowStep {f : Function} {n : Norm} (hn : NormSoundT f n) :
    RuleSoundT f (narrowStep n (atomTy f)) := by
  intro tms i x' h hord fr mem t ht hA
  cases i with
  | ireduce ty u =>
    simp only [narrowStep] at h
    split at h
    · rename_i op wty a b hu
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨⟨hring, hw⟩, hta⟩, htb⟩ := hc
        obtain ⟨a', ha', h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
        -- the value of the narrowed node `j`
        have hj : tmVal f tms fr mem t =
            evalNode (tmFrame f tms fr mem) mem (.binary op ty a' b') := by
          cases haff : affStep tms (.binary op ty a' b') with
          | some z =>
            simp only [haff, Option.orElse_some, Option.getD_some] at ht hord
            exact ruleSound_affStep tms _ z haff hord f fr mem t ht
          | none =>
            cases hsw : swapStep tms (.binary op ty a' b') with
            | some z =>
              simp only [haff, hsw, Option.orElse_none, Option.getD_some] at ht hord
              exact ruleSound_swapStep tms _ z hsw hord f fr mem t ht
            | none =>
              simp only [haff, hsw, Option.orElse_none, Option.getD_none] at ht hord
              exact tmVal_node' ht (hord t ht)
        rw [hj]
        have hna := nodeAt_spec hu
        have hru : TmReach tms (.ireduce ty u) u := .op (by simp [operands])
        have hra : TmReach tms (.ireduce ty u) a := .sub hru hna.1 (by simp [operands])
        have hrb : TmReach tms (.ireduce ty u) b := .sub hru hna.1 (by simp [operands])
        have hAa : AtomsTyped f tms fr mem (.ireduce ty a) :=
          hA.of_ops (by intro o ho; simp only [operands, List.mem_singleton] at ho; subst ho; exact hra)
        have hAb : AtomsTyped f tms fr mem (.ireduce ty b) :=
          hA.of_ops (by intro o ho; simp only [operands, List.mem_singleton] at ho; subst ho; exact hrb)
        have hav : (tmFrame f tms fr mem).regs a' =
            evalNode (tmFrame f tms fr mem) mem (.ireduce ty a) := redOf_spec hn ha' hAa
        have hbv : (tmFrame f tms fr mem).regs b' =
            evalNode (tmFrame f tms fr mem) mem (.ireduce ty b) := redOf_spec hn hb' hAb
        have huv : (tmFrame f tms fr mem).regs u =
            evalNode (tmFrame f tms fr mem) mem (.binary op wty a b) := tmVal_node hna.1 hna.2
        have hop := ringOp_nonShift hring
        rw [evalNode_binary_nonShift hop, hav, hbv, evalNode_ireduce, evalNode_ireduce,
          evalNode_ireduce, huv, evalNode_binary_nonShift hop]
        rcases hva : (tmFrame f tms fr mem).regs a with _ | va
        · simp
        · have hvat : va.ty = wty := tyAt_val hA hra hta hva
          obtain ⟨vat, A⟩ := va
          simp only at hvat
          subst hvat
          rcases hvb : (tmFrame f tms fr mem).regs b with _ | vb
          · simp [hw]
          · have hvbt : vb.ty = vat := tyAt_val hA hrb htb hvb
            obtain ⟨vbt, B⟩ := vb
            simp only at hvbt
            subst hvbt
            simp [hw, setWidth_ring hring (Nat.le_of_lt hw)]
      · cases h
    · cases h
  | _ => simp [narrowStep] at h

end Opt.MidVal

import FV.Opt.Proof.MidValRel
import FV.Opt.Proof.GvnEditX
import FV.Opt.Proof.SimWinU

/-!
# Terminators and block entry of the mid-end validator (#1119, module (5), slice E)

* `rel_enter`: from both frames at the end of block `bi` (`AtEnd`: `f` after its body, `g` after
  its whole checked pure tail), entering a successor `bc`/`bc'` of the same block with the same
  argument values gives frames related at the start of the successor `si` with its entry facts,
  at any memory where the memory facts kept on the edge hold (`m' = m` for a branch; any memory
  after a `try_call`, whose edges keep no memory fact). The entry facts and the values of `f`
  that are not parameters of `si` have terms whose sites are in strict dominators of `si`
  (`entryOk`, `sitesF`/`sitesG`), so entering `si` keeps their values (`TV_enter`); the
  parameters' terms are `param si i` on both sides (`blockOk`), bound to the same arguments.
* `rel_term`: `g` runs its pure tail (`GPreRun`), then the terminators, equal on terms
  (`EndOk`), read equal operand values, take the same branch with equal arguments, return the
  same values, tail-call alike, trap alike (`term_step`).
* `rel_try`: `try_call`/`try_call_indirect`. The results (normal edge) and the exception payload
  (handler edges) are bound at each function's fresh value; a successor argument `.ret i` or
  `.exn i` reads that window also beyond the results, so the relation is `MRW = MR ∧ Win`
  (equal windows, `FV/Opt/Proof/SimWin.lean`). The normal and handler edges are block entries
  (`rel_enter`) from the frames with the window bound (`AtEnd.regs_congr`).
-/

namespace Opt.MidVal

open Clif

/-- The frame relation with equal fresh-value windows (`Opt.Win`): the relation of the
`try_call` obligations. -/
def MRW (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm) (syms : String → Option Nat)
    (fr fr' : Frame) (m : Mem) : Prop :=
  MR f g fi gi cert norm syms fr fr' m ∧ Win fr fr'

/-- Both frames at the end of block `bi`: `f` after its body, `g` after its whole body. -/
structure AtEnd (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm)
    (syms : String → Option Nat) (bi : Nat) (fb gb : Block) (S : List Fact) (fr fr' : Frame)
    (m : Mem) : Prop where
  hfb : f.blocks[bi]? = some fb
  hgb : g.blocks[bi]? = some gb
  endOk : EndOk (ccOf fi gi cert norm) bi fb gb S
  invf : Inv f (wfData f fi) syms fr bi fb.body.length
  invg : Inv g (wfData g gi) syms fr' bi gb.body.length
  slots : fr'.slots = fr.slots
  agreeF : ∀ x, Avail (wfData f fi) bi fb.body.length x →
    TV f cert syms fr ((ccOf fi gi cert norm).ef x) = fr.regs x
  agreeG : ∀ y, Avail (wfData g gi) bi gb.body.length y →
    TV f cert syms fr ((ccOf fi gi cert norm).eg y) = fr'.regs y
  sitesG : ∀ y, Avail (wfData g gi) bi gb.body.length y →
    LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y))
      (bi, fb.body.length)
  facts : ∀ F ∈ S, FactHolds f cert syms fr m F
  factSites : ∀ F ∈ S, ∀ t ∈ F.terms,
    LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf t) (bi, fb.body.length)

namespace Tn

/-! ## Helpers -/

theorem inv_end {syms : String → Option Nat} {F : Function} {W : WfData} {fr : Frame} {bi : Nat}
    {b : Block} (h : Inv F W syms fr bi b.body.length) (hb : F.blocks[bi]? = some b) :
    fr.body = [] ∧ fr.term = b.term := by
  obtain ⟨b', hb', hbody, hterm, -⟩ := h.block
  rw [hb] at hb'
  cases hb'
  exact ⟨by rw [hbody]; simp, hterm⟩

theorem inB_of_inv {syms : String → Option Nat} {F : Function} {W : WfData} {fr : Frame}
    {bi k : Nat} (h : Inv F W syms fr bi k) : InB fr := by
  obtain ⟨b, hb, hbody, hterm, -⟩ := h.block
  refine ⟨trivial, b, ?_, by rw [hbody]; exact List.drop_suffix _ _, hterm⟩
  rw [h.func]
  exact List.mem_of_getElem? hb

theorem pw2_of_map {σf σg : ValueId → Nat} {P : ValueId → ValueId → Prop} :
    ∀ {xs ys : List ValueId}, xs.map σf = ys.map σg →
      (∀ x ∈ xs, ∀ y ∈ ys, σf x = σg y → P x y) → Pw2 P xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons (hp x (by simp) y (by simp) h.1)
      (pw2_of_map h.2 fun a ha b hb hab => hp a (by simp [ha]) b (by simp [hb]) hab)

theorem getMany_norm {A B : Frame} {xs ys : List ValueId}
    (h : Pw2 (fun x y => B.regs y = A.regs x) xs ys) :
    (B.getMany ys).norm = (A.getMany xs).norm := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    simp only [Frame.getMany, Frame.get, hxy, Res.norm_bind, Res.norm_ofOption, ih]

theorem tailArgs_pw {A B : Frame} {fn : FnRef} {xs ys : List ValueId}
    (hx : B.func.externs = A.func.externs) (hs : B.func.sig = A.func.sig)
    (h : Pw2 (fun x y => B.regs y = A.regs x) xs ys) :
    (tailArgs B fn ys).norm = (tailArgs A fn xs).norm := by
  simp only [tailArgs, Function.extern?, hx, hs, Res.norm_bind, Res.norm_ofOption, checkTys,
    Res.norm_check, Res.norm_pure, getMany_norm h]

theorem callArgs_pw {A B : Frame} {fn : FnRef} {xs ys : List ValueId}
    (hx : B.func.externs = A.func.externs) (h : Pw2 (fun x y => B.regs y = A.regs x) xs ys) :
    (callArgs B fn ys).norm = (callArgs A fn xs).norm := by
  simp only [callArgs, Function.extern?, hx, Res.norm_bind, Res.norm_ofOption, checkTys,
    Res.norm_check, Res.norm_pure, getMany_norm h]

theorem ciArgs_pw {A B : Frame} {sig : Nat} {c c' : ValueId} {xs ys : List ValueId}
    {r : Signature × Nat × List Val} (hsd : B.func.sigDecls = A.func.sigDecls)
    (hc : B.regs c' = A.regs c) (h : Pw2 (fun x y => B.regs y = A.regs x) xs ys)
    (ha : ciArgs A sig c xs = .ok r) : ciArgs B sig c' ys = .ok r := by
  obtain ⟨d, a, vals⟩ := r
  obtain ⟨cv, cv64, hd, hcv, h64, rfl, hv⟩ := ciArgs_ok.1 ha
  exact ciArgs_ok.2 ⟨cv, cv64, by rw [hsd]; exact hd, by rw [hc]; exact hcv, h64, rfl,
    getMany_pw2 h hv⟩

theorem mbc {σf σg : ValueId → Nat} {bc bc' : BlockCall}
    (h : mapBlockCall σf bc = mapBlockCall σg bc') :
    bc'.block = bc.block ∧ bc.args.map σf = bc'.args.map σg :=
  ⟨(congrArg BlockCall.block h).symm, congrArg BlockCall.args h⟩

theorem ofRes_cases {α : Type} {x : Res α} {k : α → LRes} {r : LRes}
    (hx : ∀ c, x ≠ .trap c) (h : LRes.ofRes x k = r) :
    (∃ a, x = .ok a ∧ k a = r) ∨ ∃ s, r = .stuck s := by
  cases x with
  | ok a => exact .inl ⟨a, rfl, h⟩
  | trap c => exact absurd rfl (hx c)
  | stuck s => exact .inr ⟨s, h.symm⟩

theorem sel_pair {σf σg : ValueId → Nat} {d d' : BlockCall} {tbl tbl' : List BlockCall}
    (hd : mapBlockCall σf d = mapBlockCall σg d')
    (ht : tbl.map (mapBlockCall σf) = tbl'.map (mapBlockCall σg)) (n : Nat) :
    mapBlockCall σf (tbl[n]?.getD d) = mapBlockCall σg (tbl'[n]?.getD d') ∧
      (tbl[n]?.getD d = d ∨ tbl[n]?.getD d ∈ tbl) ∧
      (tbl'[n]?.getD d' = d' ∨ tbl'[n]?.getD d' ∈ tbl') := by
  have h := congrArg (·[n]?) ht
  simp only [List.getElem?_map] at h
  cases h1 : tbl[n]? <;> cases h2 : tbl'[n]? <;> rw [h1, h2] at h
  · exact ⟨hd, .inl rfl, .inl rfl⟩
  · simp at h
  · simp at h
  · exact ⟨Option.some.inj h, .inr (List.mem_of_getElem? h1), .inr (List.mem_of_getElem? h2)⟩

/-- `TryDest.mapVals` on one argument. -/
def targ (σ : ValueId → Nat) (a : TryArg) : TryArg :=
  match a with
  | .val v => .val (σ v)
  | a => a

theorem mapVals_args (σ : ValueId → Nat) (d : TryDest) :
    (d.mapVals σ).args = d.args.map (targ σ) := by
  show List.map _ d.args = List.map (targ σ) d.args
  exact congrArg (List.map · d.args) (funext fun a => by cases a <;> rfl)

theorem val_mem_vals {d : TryDest} {v : ValueId} (h : TryArg.val v ∈ d.args) : v ∈ d.vals :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

/-- The arguments of normal-return successors whose tables are equal on terms. -/
theorem resolve_pair2 {σf σg : ValueId → Nat} (b1 b2 : ValueId) :
    ∀ (l1 l2 : List TryArg) (xs : List ValueId), l1.map (targ σf) = l2.map (targ σg) →
      resolve b1 l1 = .ok xs →
      ∃ ys, resolve b2 l2 = .ok ys ∧
        Pw2 (fun x y => (∃ v w, TryArg.val v ∈ l1 ∧ TryArg.val w ∈ l2 ∧ x = v ∧ y = w ∧
          σf v = σg w) ∨ ∃ i, x = b1 + i ∧ y = b2 + i) xs ys
  | [], [], xs, _, h => by
    simp only [resolve] at h
    cases h
    exact ⟨[], rfl, .nil⟩
  | [], _ :: _, _, hm, _ => by simp at hm
  | _ :: _, [], _, hm, _ => by simp at hm
  | a :: l1, b :: l2, xs, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨hab, hm⟩ := hm
    simp only [resolve, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨ys, hys, hp⟩ := resolve_pair2 b1 b2 l1 l2 xs' hm hxs
    have hp' : Pw2 (fun x y => (∃ v w, TryArg.val v ∈ a :: l1 ∧ TryArg.val w ∈ b :: l2 ∧
        x = v ∧ y = w ∧ σf v = σg w) ∨ ∃ i, x = b1 + i ∧ y = b2 + i) xs' ys :=
      hp.imp fun x y h => by
        rcases h with ⟨v, w, h1, h2, h3, h4, h5⟩ | h
        · exact .inl ⟨v, w, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3, h4, h5⟩
        · exact .inr h
    cases a with
    | val v =>
      simp only [Res.pure_eq_ok] at hx
      subst hx
      cases b with
      | val w =>
        have hab' : TryArg.val (σf v) = TryArg.val (σg w) := hab
        simp only [TryArg.val.injEq] at hab'
        refine ⟨w :: ys, ?_, .cons (.inl ⟨v, w, by simp, by simp, rfl, rfl, hab'⟩) hp'⟩
        simp only [resolve, hys]
        rfl
      | ret i =>
        have hab' : TryArg.val (σf v) = TryArg.ret i := hab
        cases hab'
      | exn i =>
        have hab' : TryArg.val (σf v) = TryArg.exn i := hab
        cases hab'
    | ret i =>
      simp only [Res.pure_eq_ok] at hx
      subst hx
      cases b with
      | val w =>
        have hab' : TryArg.ret i = TryArg.val (σg w) := hab
        cases hab'
      | ret j =>
        have hab' : TryArg.ret i = TryArg.ret j := hab
        simp only [TryArg.ret.injEq] at hab'
        subst hab'
        refine ⟨(b2 + i) :: ys, ?_, .cons (.inr ⟨i, rfl, rfl⟩) hp'⟩
        simp only [resolve, hys]
        rfl
      | exn j =>
        have hab' : TryArg.ret i = TryArg.exn j := hab
        cases hab'
    | exn i => cases hx

/-- The arguments of handler successors whose tables are equal on terms. -/
theorem resolveH_pair2 {σf σg : ValueId → Nat} (b1 b2 : ValueId) :
    ∀ (l1 l2 : List TryArg) (xs : List ValueId), l1.map (targ σf) = l2.map (targ σg) →
      resolveH b1 l1 = .ok xs →
      ∃ ys, resolveH b2 l2 = .ok ys ∧
        Pw2 (fun x y => (∃ v w, TryArg.val v ∈ l1 ∧ TryArg.val w ∈ l2 ∧ x = v ∧ y = w ∧
          σf v = σg w) ∨ ∃ i, x = b1 + i ∧ y = b2 + i) xs ys
  | [], [], xs, _, h => by
    simp only [resolveH] at h
    cases h
    exact ⟨[], rfl, .nil⟩
  | [], _ :: _, _, hm, _ => by simp at hm
  | _ :: _, [], _, hm, _ => by simp at hm
  | a :: l1, b :: l2, xs, hm, h => by
    simp only [List.map_cons, List.cons.injEq] at hm
    obtain ⟨hab, hm⟩ := hm
    simp only [resolveH, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨ys, hys, hp⟩ := resolveH_pair2 b1 b2 l1 l2 xs' hm hxs
    have hp' : Pw2 (fun x y => (∃ v w, TryArg.val v ∈ a :: l1 ∧ TryArg.val w ∈ b :: l2 ∧
        x = v ∧ y = w ∧ σf v = σg w) ∨ ∃ i, x = b1 + i ∧ y = b2 + i) xs' ys :=
      hp.imp fun x y h => by
        rcases h with ⟨v, w, h1, h2, h3, h4, h5⟩ | h
        · exact .inl ⟨v, w, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, h3, h4, h5⟩
        · exact .inr h
    cases a with
    | val v =>
      simp only [Res.pure_eq_ok] at hx
      subst hx
      cases b with
      | val w =>
        have hab' : TryArg.val (σf v) = TryArg.val (σg w) := hab
        simp only [TryArg.val.injEq] at hab'
        refine ⟨w :: ys, ?_, .cons (.inl ⟨v, w, by simp, by simp, rfl, rfl, hab'⟩) hp'⟩
        simp only [resolveH, hys]
        rfl
      | ret i =>
        have hab' : TryArg.val (σf v) = TryArg.ret i := hab
        cases hab'
      | exn i =>
        have hab' : TryArg.val (σf v) = TryArg.exn i := hab
        cases hab'
    | exn i =>
      simp only [Res.pure_eq_ok] at hx
      subst hx
      cases b with
      | val w =>
        have hab' : TryArg.exn i = TryArg.val (σg w) := hab
        cases hab'
      | exn j =>
        have hab' : TryArg.exn i = TryArg.exn j := hab
        simp only [TryArg.exn.injEq] at hab'
        subst hab'
        refine ⟨(b2 + i) :: ys, ?_, .cons (.inr ⟨i, rfl, rfl⟩) hp'⟩
        simp only [resolveH, hys]
        rfl
      | ret j =>
        have hab' : TryArg.exn i = TryArg.ret j := hab
        cases hab'
    | ret i => cases hx

theorem tryNormal_pair2 {σf σg : ValueId → Nat} {et et' : ExnTable}
    (hn : et.normal.mapVals σf = et'.normal.mapVals σg) {b1 b2 : ValueId} {bc1 : BlockCall}
    (h : tryNormal et b1 = .ok bc1) :
    ∃ bc2, tryNormal et' b2 = .ok bc2 ∧ bc2.block = bc1.block ∧
      Pw2 (fun x y => (∃ v w, v ∈ et.normal.vals ∧ w ∈ et'.normal.vals ∧ x = v ∧ y = w ∧
        σf v = σg w) ∨ ∃ i, x = b1 + i ∧ y = b2 + i) bc1.args bc2.args := by
  rw [tryNormal_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args1, hm1, rfl⟩ := h
  have hb : et.normal.block = et'.normal.block := by
    have := congrArg TryDest.block hn
    exact this
  have ha : et.normal.args.map (targ σf) = et'.normal.args.map (targ σg) := by
    rw [← mapVals_args, ← mapVals_args, hn]
  obtain ⟨ys, hys, hp⟩ := resolve_pair2 b1 b2 _ _ _ ha hm1
  refine ⟨{ block := et'.normal.block, args := ys }, by simp only [Res.bind_eq_ok]; exact ⟨ys, hys, rfl⟩,
    hb.symm, hp.imp fun x y hq => ?_⟩
  rcases hq with ⟨v, w, hv, hw, h1, h2, h3⟩ | hq
  · exact .inl ⟨v, w, val_mem_vals hv, val_mem_vals hw, h1, h2, h3⟩
  · exact .inr hq

theorem tryHandler_pair2 {σf σg : ValueId → Nat} {d d' : TryDest}
    (hd : d.mapVals σf = d'.mapVals σg) {b1 b2 : ValueId} {bc1 : BlockCall}
    (h : tryHandler d b1 = .ok bc1) :
    ∃ bc2, tryHandler d' b2 = .ok bc2 ∧ bc2.block = bc1.block ∧
      Pw2 (fun x y => (∃ v w, v ∈ d.vals ∧ w ∈ d'.vals ∧ x = v ∧ y = w ∧ σf v = σg w) ∨
        ∃ i, x = b1 + i ∧ y = b2 + i) bc1.args bc2.args := by
  rw [tryHandler_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args1, hm1, rfl⟩ := h
  have hb : d.block = d'.block := by
    have := congrArg TryDest.block hd
    exact this
  have ha : d.args.map (targ σf) = d'.args.map (targ σg) := by
    rw [← mapVals_args, ← mapVals_args, hd]
  obtain ⟨ys, hys, hp⟩ := resolveH_pair2 b1 b2 _ _ _ ha hm1
  refine ⟨{ block := d'.block, args := ys }, by simp only [Res.bind_eq_ok]; exact ⟨ys, hys, rfl⟩,
    hb.symm, hp.imp fun x y hq => ?_⟩
  rcases hq with ⟨v, w, hv, hw, h1, h2, h3⟩ | hq
  · exact .inl ⟨v, w, val_mem_vals hv, val_mem_vals hw, h1, h2, h3⟩
  · exact .inr hq

theorem setMany_param {r r' : Regs} {ps : List (ValueId × Ty)} {vs : List Val}
    (h : r.setMany (ps.map (·.1)) vs = some r') {i : Nat} {p : ValueId × Ty}
    (hp : ps[i]? = some p) (hu : ∀ n q, ps[n]? = some q → q.1 = p.1 → n = i) :
    r' p.1 = vs[i]? := by
  obtain ⟨n, hn, hr⟩ :=
    ((setMany_spec h).2 p.1).2 (List.mem_map.2 ⟨p, List.mem_of_getElem? hp, rfl⟩)
  rw [List.getElem?_map, Option.map_eq_some_iff] at hn
  obtain ⟨q, hq, hqp⟩ := hn
  rw [← hu n q hq hqp]
  exact hr

theorem params_uniq {c : CC} {env : ValueId → Nat} {ps : List (ValueId × Ty)} {si : Nat}
    (hP : ∀ i p, ps[i]? = some p → c.tm (env p.1) = some (.param si i)) {i : Nat}
    {p : ValueId × Ty} (hp : ps[i]? = some p) :
    ∀ n q, ps[n]? = some q → q.1 = p.1 → n = i := by
  intro n q hq hqp
  have h1 := hP n q hq
  rw [hqp, hP i p hp] at h1
  simp only [Option.some.injEq, Tm.param.injEq] at h1
  exact h1.2.symm

/-- Binding a `try_call`'s results (or a payload) at the fresh value keeps the registers below. -/
theorem set_lo {A : Frame} {F : Function} (hF : A.func = F) {n : Nat} {vs : List Val} {r : Regs}
    (h : A.regs.setMany (tryRets n A.func.freshValue) vs = some r) :
    ∀ v < F.freshValue, r v = A.regs v := by
  intro v hv
  refine ((setMany_spec h).2 v).1 fun hm => ?_
  obtain ⟨j, -, hj⟩ := List.mem_map.1 hm
  have hj' : A.func.freshValue + j = v := hj
  rw [hF] at hj'
  rw [← hj'] at hv
  exact absurd hv (Nat.not_lt.2 (Nat.le_add_right _ _))

theorem win_set {A B : Frame} {n : Nat} {vs : List Val} {r r' : Regs} (hw : Win A B)
    (h : A.regs.setMany (tryRets n A.func.freshValue) vs = some r)
    (h' : B.regs.setMany (tryRets n B.func.freshValue) vs = some r') :
    Win { A with regs := r } { B with regs := r' } := by
  intro i
  show r (A.func.freshValue + i) = r' (B.func.freshValue + i)
  rw [setMany_tryRets h i, setMany_tryRets h' i]
  split
  · rfl
  · exact hw i

theorem win_enter {A B A1 B1 : Frame} {bc bc' : BlockCall} (he : enterBlock A bc = .ok A1)
    (he' : enterBlock B bc' = .ok B1) (hw : Win A B) : Win A1 B1 := by
  obtain ⟨-, hf1, -, hw1⟩ := enterBlock_win he
  obtain ⟨-, hf2, -, hw2⟩ := enterBlock_win he'
  intro i
  rw [hf1, hf2, hw1 i, hw2 i]
  exact hw i

theorem nomem {S : List Fact} {b : Bool} (hb : b = true) {m1 m : Mem} :
    ∀ F ∈ (if b then kill S else S), F.isMem = true → m1 = m := by
  intro F hF hmem
  simp only [hb, ↓reduceIte] at hF
  have := (List.mem_filter.1 hF).2
  simp [hmem] at this

/-! ## Terminators, semantically -/

/-- Two frames at the end of their blocks with terminators equal on terms and operands read
alike: their local steps agree (the branches given by `henter`). -/
theorem term_step {fr fr2 : Frame} {m : Mem} {ft gt : Terminator} {σf σg : ValueId → Nat}
    {Q : Frame → Frame → Mem → Prop}
    (hb : fr.body = []) (hb2 : fr2.body = []) (hft : fr.term = ft) (hgt : fr2.term = gt)
    (hT : mapTerm σf ft = mapTerm σg gt)
    (hops : ∀ x ∈ termOperands ft, ∀ y ∈ termOperands gt, σf x = σg y → fr2.regs y = fr.regs x)
    (hx : fr2.func.externs = fr.func.externs) (hsig : fr2.func.sig = fr.func.sig)
    (henter : ∀ bc bc' fr1, bc.block ∈ termSuccs ft → bc'.block = bc.block →
      (∀ vs, fr.getMany bc.args = .ok vs → fr2.getMany bc'.args = .ok vs) →
      enterBlock fr bc = .ok fr1 → ∃ fr1', enterBlock fr2 bc' = .ok fr1' ∧ Q fr1 fr1' m) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 → ∃ fr1', lstep fr2 m = .next fr1' m1 ∧ Q fr1 fr1' m1) ∧
    (∀ vals, lstep fr m = .ret vals → lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals → lstep fr2 m = .tail ext vals) ∧
    (∀ c, lstep fr m = .trap c → lstep fr2 m = .trap c) := by
  have hbr : ∀ bc bc', bc.block ∈ termSuccs ft → mapBlockCall σf bc = mapBlockCall σg bc' →
      (∀ x ∈ bc.args, x ∈ termOperands ft) → (∀ y ∈ bc'.args, y ∈ termOperands gt) →
      ∀ fr1 m1, LRes.ofRes (enterBlock fr bc) (fun fr' => LRes.next fr' m) = .next fr1 m1 →
        ∃ fr1', LRes.ofRes (enterBlock fr2 bc') (fun fr' => LRes.next fr' m) = .next fr1' m1 ∧
          Q fr1 fr1' m1 := by
    intro bc bc' hs hm hxs hys fr1 m1 hl
    obtain ⟨hblk, hargs⟩ := mbc hm
    rcases ofRes_cases (enterBlock_not_trap fr bc) hl with ⟨a, he, hk⟩ | ⟨s, hs'⟩
    · simp only [LRes.next.injEq] at hk
      obtain ⟨h1, h2⟩ := hk
      subst h1 h2
      obtain ⟨fr1', he', hq⟩ := henter bc bc' _ hs hblk (fun vs hv => getMany_pw2
        (pw2_of_map hargs fun x hx y hy hxy => hops x (hxs x hx) y (hys y hy) hxy) hv) he
      exact ⟨fr1', by rw [he']; rfl, hq⟩
    · cases hs'
  have hent : ∀ bc (r : LRes), LRes.ofRes (enterBlock fr bc) (fun fr' => LRes.next fr' m) = r →
      (∃ fr1, r = .next fr1 m) ∨ ∃ s, r = .stuck s := by
    intro bc r h
    rcases ofRes_cases (enterBlock_not_trap fr bc) h with ⟨a, -, hk⟩ | ⟨s, hs⟩
    · exact .inl ⟨a, hk.symm⟩
    · exact .inr ⟨s, hs⟩
  rw [lstep_term hb, lstep_term hb2, hft, hgt]
  cases ft with
  | jump d =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.jump.injEq] at hT
    rename_i d'
    dsimp only
    refine ⟨fun fr1 m1 hl => hbr d d' (by simp [termSuccs]) hT
      (fun x hx => by simpa [termOperands] using hx) (fun y hy => by simpa [termOperands] using hy)
      fr1 m1 hl, fun vals hl => ?_, fun ext vals hl => ?_, fun c hl => ?_⟩ <;>
      rcases hent d _ hl with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  | brif c t e =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.brif.injEq] at hT
    rename_i c' t' e'
    obtain ⟨hc, htt, hee⟩ := hT
    dsimp only
    have hget : ∀ cv, fr.get c = .ok cv → fr2.get c' = .ok cv := by
      intro cv h
      simp only [Frame.get, Res.ofOption_eq_ok] at h ⊢
      rw [hops c (by simp [termOperands]) c' (by simp [termOperands]) hc]
      exact h
    have hgnt : ∀ c0, fr.get c ≠ .trap c0 := fun c0 => by simp [Frame.get]
    have hsel : ∀ b : Bool, ((if b then t else e) = t ∧ (if b then t' else e') = t') ∨
        ((if b then t else e) = e ∧ (if b then t' else e') = e') := by
      intro b
      cases b
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨rfl, rfl⟩
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun ext vals hl => ?_, fun c0 hl => ?_⟩
    · rcases ofRes_cases hgnt hl with ⟨cv, hcv, hl⟩ | ⟨_, h⟩
      · rw [hget cv hcv]
        simp only [LRes.ofRes_ok]
        rcases hsel (Sem.truthy cv.bits) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hl
          rw [h2]
          exact hbr t t' (by simp [termSuccs]) htt (fun x hx => by simp [termOperands, hx])
            (fun y hy => by simp [termOperands, hy]) fr1 m1 hl
        · rw [h1] at hl
          rw [h2]
          exact hbr e e' (by simp [termSuccs]) hee (fun x hx => by simp [termOperands, hx])
            (fun y hy => by simp [termOperands, hy]) fr1 m1 hl
      · cases h
    all_goals
      rcases ofRes_cases hgnt hl with ⟨cv, -, hl⟩ | ⟨_, h⟩
      · rcases hent _ _ hl with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      · cases h
  | brTable x d tbl =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.brTable.injEq] at hT
    rename_i x' d' tbl'
    obtain ⟨hxx, hdd, htb⟩ := hT
    dsimp only
    have hget : ∀ xv, fr.get x = .ok xv → fr2.get x' = .ok xv := by
      intro xv h
      simp only [Frame.get, Res.ofOption_eq_ok] at h ⊢
      rw [hops x (by simp [termOperands]) x' (by simp [termOperands]) hxx]
      exact h
    have hgnt : ∀ c0, fr.get x ≠ .trap c0 := fun c0 => by simp [Frame.get]
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun ext vals hl => ?_, fun c0 hl => ?_⟩
    · rcases ofRes_cases hgnt hl with ⟨xv, hxv, hl⟩ | ⟨_, h⟩
      · rw [hget xv hxv]
        simp only [LRes.ofRes_ok]
        obtain ⟨hs, hm, hm'⟩ := sel_pair hdd htb xv.toNat
        refine hbr _ _ ?_ hs ?_ ?_ fr1 m1 hl
        · rcases hm with hm | hm
          · rw [hm]; simp [termSuccs]
          · simp only [termSuccs, List.mem_cons, List.mem_map]
            exact .inr ⟨_, hm, rfl⟩
        · intro z hz
          simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
          rcases hm with hm | hm
          · rw [hm] at hz; exact .inl (.inr hz)
          · exact .inr ⟨_, hm, hz⟩
        · intro z hz
          simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
          rcases hm' with hm' | hm'
          · rw [hm'] at hz; exact .inl (.inr hz)
          · exact .inr ⟨_, hm', hz⟩
      · cases h
    all_goals
      rcases ofRes_cases hgnt hl with ⟨xv, -, hl⟩ | ⟨_, h⟩
      · rcases hent _ _ hl with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
      · cases h
  | ret xs =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.ret.injEq] at hT
    rename_i xs'
    dsimp only
    have hpw : Pw2 (fun x y => fr2.regs y = fr.regs x) xs xs' :=
      pw2_of_map hT fun x hx y hy hxy =>
        hops x (by simpa [termOperands] using hx) y (by simpa [termOperands] using hy) hxy
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun ext vals hl => ?_, fun c0 hl => ?_⟩
    · rcases ofRes_cases (getMany_not_trap fr xs) hl with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    · rcases ofRes_cases (getMany_not_trap fr xs) hl with ⟨vs, hvs, hk⟩ | ⟨_, h⟩
      · rw [getMany_pw2 hpw hvs]
        exact hk
      · cases h
    · rcases ofRes_cases (getMany_not_trap fr xs) hl with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
    · rcases ofRes_cases (getMany_not_trap fr xs) hl with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
  | returnCall fn args =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.returnCall.injEq] at hT
    rename_i fn' args'
    obtain ⟨rfl, hargs⟩ := hT
    dsimp only
    have hpw : Pw2 (fun x y => fr2.regs y = fr.regs x) args args' :=
      pw2_of_map hargs fun x hx y hy hxy =>
        hops x (by simpa [termOperands] using hx) y (by simpa [termOperands] using hy) hxy
    have htn : ∀ c0, tailArgs fr fn args ≠ .trap c0 := fun c0 => by simp [tailArgs, checkTys]
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun ext vals hl => ?_, fun c0 hl => ?_⟩
    · rcases ofRes_cases htn hl with ⟨⟨_, _⟩, _, h⟩ | ⟨_, h⟩ <;> cases h
    · rcases ofRes_cases htn hl with ⟨⟨_, _⟩, _, h⟩ | ⟨_, h⟩ <;> cases h
    · rcases ofRes_cases htn hl with ⟨a, ha, hk⟩ | ⟨_, h⟩
      · rw [Res.norm_eq_ok (tailArgs_pw hx hsig hpw) ha]
        exact hk
      · cases h
    · rcases ofRes_cases htn hl with ⟨⟨_, _⟩, _, h⟩ | ⟨_, h⟩ <;> cases h
  | trap c =>
    cases gt <;> simp only [mapTerm, reduceCtorEq, Terminator.trap.injEq] at hT
    subst hT
    exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h),
      fun _ h => h⟩
  | tryCall _ _ _ =>
    exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h),
      fun _ h => (by cases h)⟩
  | tryCallIndirect _ _ _ =>
    exact ⟨fun _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h),
      fun _ h => (by cases h)⟩

/-! ## Blocks and dominance -/

section
variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm} {syms : String → Option Nat}

theorem id_eqT (H : HypT f g fi gi cert norm) {i : Nat} {b gb : Block}
    (hb : f.blocks[i]? = some b) (hg : g.blocks[i]? = some gb) : gb.id = b.id := by
  have h := congrArg (·[i]?) H.ok.ids
  simp only [List.getElem?_map, hb, hg, Option.map_some] at h
  exact Option.some.inj h

theorem id_eq (H : Hyp f g fi gi cert norm) {i : Nat} {b gb : Block}
    (hb : f.blocks[i]? = some b) (hg : g.blocks[i]? = some gb) : gb.id = b.id := by
  exact id_eqT H.toT hb hg

theorem block?_gT (H : HypT f g fi gi cert norm) {id : BlockId} {j : Nat} {b gb : Block}
    (hf : f.block? id = some b) (hj : f.blocks[j]? = some b) (hj' : g.blocks[j]? = some gb) :
    g.block? id = some gb := by
  obtain ⟨j0, hj0, hid⟩ := H.wff.block?_index hf
  have := H.wff.idx_unique hj0 hj rfl
  subst this
  rw [Function.block?, List.find?_eq_some_iff_getElem] at hf ⊢
  obtain ⟨hp, i, hi, hbi, hlt⟩ := hf
  have hij : i = j0 := H.wff.idx_unique (by simp [hi, hbi]) hj0 rfl
  subst hij
  have hid' : gb.id = b.id := id_eqT H hj0 hj'
  have hi' : i < g.blocks.length := (List.getElem?_eq_some_iff.1 hj').1
  refine ⟨by simpa [hid'] using hp, i, hi', by simpa [hi'] using hj', fun j2 hj2 => ?_⟩
  have hj2f : j2 < f.blocks.length := by omega
  have hid2 : g.blocks[j2].id = f.blocks[j2].id :=
    id_eqT H (List.getElem?_eq_getElem hj2f) (List.getElem?_eq_getElem (by omega))
  have := hlt j2 hj2
  rw [hid2]
  exact this

theorem block?_g (H : Hyp f g fi gi cert norm) {id : BlockId} {j : Nat} {b gb : Block}
    (hf : f.block? id = some b) (hj : f.blocks[j]? = some b) (hj' : g.blocks[j]? = some gb) :
    g.block? id = some gb := by
  exact block?_gT H.toT hf hj hj'

theorem strict_of_leT (H : HypT f g fi gi cert norm) {a : Nat × Nat} {d t si : Nat}
    (h : LeP fi.cfg.idom a (d, t)) (hne : d ≠ si) (ha : Anc fi.cfg.idom d si) :
    a.1 ≠ si ∧ Anc fi.cfg.idom a.1 si := by
  rcases h with ⟨e, -⟩ | ⟨-, an⟩
  · rw [e]
    exact ⟨hne, ha⟩
  · refine ⟨fun he => ?_, an.trans ha⟩
    rw [he] at an
    exact hne (Anc.antisymm H.rankF ha an)

theorem strict_of_le (H : Hyp f g fi gi cert norm) {a : Nat × Nat} {d t si : Nat}
    (h : LeP fi.cfg.idom a (d, t)) (hne : d ≠ si) (ha : Anc fi.cfg.idom d si) :
    a.1 ≠ si ∧ Anc fi.cfg.idom a.1 si := by
  exact strict_of_leT H.toT h hne ha

theorem strict_of_ancT (H : HypT f g fi gi cert norm) {a d si : Nat} (h : Anc fi.cfg.idom a d)
    (hne : d ≠ si) (ha : Anc fi.cfg.idom d si) : a ≠ si ∧ Anc fi.cfg.idom a si := by
  refine ⟨fun he => ?_, h.trans ha⟩
  rw [he] at h
  exact hne (Anc.antisymm H.rankF ha h)

theorem strict_of_anc (H : Hyp f g fi gi cert norm) {a d si : Nat} (h : Anc fi.cfg.idom a d)
    (hne : d ≠ si) (ha : Anc fi.cfg.idom d si) : a ≠ si ∧ Anc fi.cfg.idom a si := by
  exact strict_of_ancT H.toT h hne ha

/-- Entering block `si` (rebinding only its parameters) keeps the value of every term whose
site is in a strict dominator of `si`. -/
theorem TV_enterT (H : HypT f g fi gi cert norm) {fr fr1 : Frame} {si : Nat} {b2 : Block}
    (hg : fr1.func = fr.func) (hs : fr1.slots = fr.slots) (hj : f.blocks[si]? = some b2)
    (hr : ∀ v, v ∉ b2.params.map (·.1) → fr1.regs v = fr.regs v) {t : Nat}
    (hne : ((ccOf fi gi cert norm).siteOf t).1 ≠ si)
    (ha : Anc fi.cfg.idom ((ccOf fi gi cert norm).siteOf t).1 si) :
    TV f cert syms fr1 t = TV f cert syms fr t := by
  refine H.TV_stable (fr1 := fr) (fr2 := fr1) (by rw [hg]) (by rw [hg]) hs
    (i := ((ccOf fi gi cert norm).siteOf t).1) (k := ((ccOf fi gi cert norm).siteOf t).2)
    (fun v hv => hr v ?_) (LeP.refl _ _)
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  have hdp := H.wff.site_param hj hp
  obtain ⟨d2, t2, hd2, hva⟩ := hv
  rw [hdp] at hd2
  simp only [Option.some.injEq, Prod.mk.injEq] at hd2
  obtain ⟨h1, -⟩ := hd2
  subst h1
  rcases hva with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hne h1.symm
  · exact hne (Anc.antisymm H.rankF ha h2)

/-- Entering block `si` (rebinding only its parameters) keeps the value of every term whose
site is in a strict dominator of `si`. -/
theorem TV_enter (H : Hyp f g fi gi cert norm) {fr fr1 : Frame} {si : Nat} {b2 : Block}
    (hg : fr1.func = fr.func) (hs : fr1.slots = fr.slots) (hj : f.blocks[si]? = some b2)
    (hr : ∀ v, v ∉ b2.params.map (·.1) → fr1.regs v = fr.regs v) {t : Nat}
    (hne : ((ccOf fi gi cert norm).siteOf t).1 ≠ si)
    (ha : Anc fi.cfg.idom ((ccOf fi gi cert norm).siteOf t).1 si) :
    TV f cert syms fr1 t = TV f cert syms fr t := by
  exact TV_enterT H.toT hg hs hj hr hne ha

/-- A node without operands has the same value in frames of the same function and slots. -/
theorem TV_closed {fr fr1 : Frame} (hg : fr1.func = fr.func) (hs : fr1.slots = fr.slots) {t : Nat}
    (hcl : (ccOf fi gi cert norm).closed t = true) : TV f cert syms fr1 t = TV f cert syms fr t := by
  simp only [CC.closed, CC.tm, ccOf] at hcl
  split at hcl
  · rename_i i hi
    have hops : operands i = [] := by simpa using hcl
    show tmVal f cert.tms fr1 (symMem syms) t = tmVal f cert.tms fr (symMem syms) t
    rw [tmVal_node hi (by simp [hops]), tmVal_node hi (by simp [hops])]
    exact evalNode_congr (by simp [tmFrame, hg]) (by simp [tmFrame, hg]) (by simp [tmFrame, hs])
      (fun o ho => by simp [hops] at ho)
  · cases hcl

theorem tv_param {fr : Frame} {t si i : Nat} {b : Block} {p : ValueId × Ty}
    (ht : cert.tms[t]? = some (.param si i)) (hb : f.blocks[si]? = some b)
    (hp : b.params[i]? = some p) : TV f cert syms fr t = fr.regs p.1 := by
  rw [TV, tmVal_atom ht (fun _ h => by cases h)]
  simp [atomVal, hb, hp]

/-- `FactHolds.stable` from the values of the fact's terms. -/
theorem factHolds_of_TV {fr1 fr2 : Frame} {m1 m2 : Mem}
    (hg : fr2.func.globals = fr1.func.globals) (hx : fr2.func.externs = fr1.func.externs)
    (hs : fr2.slots = fr1.slots) {F : Fact}
    (hTV : ∀ t ∈ F.terms, TV f cert syms fr2 t = TV f cert syms fr1 t)
    (hm : F.isMem = true → m2 = m1) (h : FactHolds f cert syms fr1 m1 F) :
    FactHolds f cert syms fr2 m2 F := by
  have hfr : ∀ (i' : Inst), (∀ o ∈ operands i', o ∈ F.terms) →
      evalInst (tmFrame f cert.tms fr2 (symMem syms)) (symMem syms) i' =
        evalInst (tmFrame f cert.tms fr1 (symMem syms)) (symMem syms) i' := by
    intro i' hops
    exact evalInst_congr (by simp [tmFrame, hg]) (by simp [tmFrame, hx]) (by simp [tmFrame, hs])
      fun o ho => by simp only [tmFrame]; exact hTV o (hops o ho)
  cases F with
  | mem a off ty kd e v =>
    obtain ⟨av, vv, ha, hv, hh⟩ := h
    rw [hm rfl]
    exact ⟨av, vv, by rw [hTV a (by simp [Fact.terms]), ha], by rw [hTV v (by simp [Fact.terms]), hv], hh⟩
  | eqn i' r =>
    cases r with
    | none =>
      simp only [FactHolds] at h ⊢
      rw [hfr i' (fun o ho => by simp [Fact.terms, ho])]
      exact h
    | some t =>
      obtain ⟨v, hv, he⟩ := h
      refine ⟨v, by rw [hTV t (by simp [Fact.terms]), hv], ?_⟩
      rw [hfr i' (fun o ho => by simp [Fact.terms, ho])]
      exact he
  | defd t =>
    simp only [FactHolds] at h ⊢
    rw [hTV t (by simp [Fact.terms])]
    exact h

end

end Tn

open Tn

section
variable {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm} {syms : String → Option Nat}

/-- Related frames are at program points of their functions. -/
theorem MR.inB {fr fr' : Frame} {m : Mem} (h : MR f g fi gi cert norm syms fr fr' m) :
    InB fr ∧ InB fr' := by
  obtain ⟨_, _, _, _, hR⟩ := h
  exact ⟨inB_of_inv hR.invf, inB_of_inv hR.invg⟩

/-! ## The end of a block -/

/-- The terminators' operands read equal values. -/
theorem AtEnd.opsT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr' : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m) :
    ∀ x ∈ termOperands fb.term, ∀ y ∈ termOperands gb.term,
      (ccOf fi gi cert norm).ef x = (ccOf fi gi cert norm).eg y → fr'.regs y = fr.regs x := by
  intro x hx y hy hxy
  rw [← hE.agreeG y (H.wfg.termUses bi gb hE.hgb y hy),
    ← hE.agreeF x (H.wff.termUses bi fb hE.hfb x hx), hxy]

/-- The terminators' operands read equal values. -/
theorem AtEnd.ops (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr' : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m) :
    ∀ x ∈ termOperands fb.term, ∀ y ∈ termOperands gb.term,
      (ccOf fi gi cert norm).ef x = (ccOf fi gi cert norm).eg y → fr'.regs y = fr.regs x := by
  exact AtEnd.opsT H.toT hE

/-- Registers from the fresh values on are not read. -/
theorem AtEnd.regs_congrT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block}
    {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m) {r r' : Regs}
    (hr : ∀ v < f.freshValue, r v = fr.regs v) (hr' : ∀ v < g.freshValue, r' v = fr'.regs v) :
    AtEnd f g fi gi cert norm syms bi fb gb S { fr with regs := r } { fr' with regs := r' } m where
  hfb := hE.hfb
  hgb := hE.hgb
  endOk := hE.endOk
  invf := H.wff.inv_regs_congr hE.invf hr
  invg := H.wfg.inv_regs_congr hE.invg hr'
  slots := hE.slots
  agreeF x hx := by
    rw [H.TV_stable (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
      (fun v hv => hr v (H.wff.avail_lt hv)) (H.siteF hx), hE.agreeF x hx]
    exact (hr x (H.wff.avail_lt hx)).symm
  agreeG y hy := by
    rw [H.TV_stable (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
      (fun v hv => hr v (H.wff.avail_lt hv)) (hE.sitesG y hy), hE.agreeG y hy]
    exact (hr' y (H.wfg.avail_lt hy)).symm
  sitesG := hE.sitesG
  facts F hF := FactHolds.stableT H (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
    (fun v hv => hr v (H.wff.avail_lt hv)) (hE.factSites F hF) (fun _ => rfl) (hE.facts F hF)
  factSites := hE.factSites

/-- Registers from the fresh values on are not read. -/
theorem AtEnd.regs_congr (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block}
    {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m) {r r' : Regs}
    (hr : ∀ v < f.freshValue, r v = fr.regs v) (hr' : ∀ v < g.freshValue, r' v = fr'.regs v) :
    AtEnd f g fi gi cert norm syms bi fb gb S { fr with regs := r } { fr' with regs := r' } m where
  hfb := hE.hfb
  hgb := hE.hgb
  endOk := hE.endOk
  invf := H.wff.inv_regs_congr hE.invf hr
  invg := H.wfg.inv_regs_congr hE.invg hr'
  slots := hE.slots
  agreeF x hx := by
    rw [H.TV_stable (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
      (fun v hv => hr v (H.wff.avail_lt hv)) (H.siteF hx), hE.agreeF x hx]
    exact (hr x (H.wff.avail_lt hx)).symm
  agreeG y hy := by
    rw [H.TV_stable (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
      (fun v hv => hr v (H.wff.avail_lt hv)) (hE.sitesG y hy), hE.agreeG y hy]
    exact (hr' y (H.wfg.avail_lt hy)).symm
  sitesG := hE.sitesG
  facts F hF := FactHolds.stable H (fr1 := fr) (fr2 := { fr with regs := r }) rfl rfl rfl
    (fun v hv => hr v (H.wff.avail_lt hv)) (hE.factSites F hF) (fun _ => rfl) (hE.facts F hF)
  factSites := hE.factSites

/-- From the relation with `f` at the end of its body, `g` runs its pure tail. -/
theorem AtEnd.of_relT (H : HypT f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = []) :
    ∃ fb gb fr2, LStar fr' m fr2 m ∧ AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m := by
  obtain ⟨fb, gb, Send, hfb, hgb, hw, hend⟩ := hR.walk
  obtain ⟨fb', hfb', hbody, -, hk⟩ := hR.invf.block
  rw [hfb] at hfb'
  cases hfb'
  have hk' : k = fb.body.length := by
    rw [hb] at hbody
    have := congrArg List.length hbody
    simp at this
    omega
  subst hk'
  rw [List.drop_length] at hw
  obtain ⟨rfl, k'', hg⟩ := walk_nil_spec hw
  obtain ⟨gb', hgb', hbody', -, -⟩ := hR.invg.block
  rw [hgb] at hgb'
  cases hgb'
  obtain ⟨fr2, hst, hb2, -, hsl2, -, hinv2, hag2, hsite2⟩ :=
    hrun hm hR.invf hR.invg hR.slots hR.agreeG hR.sitesG (fun t ht => hR.facts _ ht)
      (by rw [hbody']; exact hg)
  have hk'' : k'' = gb.body.length := by
    obtain ⟨gb', hgb', hbody'', -, hk2⟩ := hinv2.block
    rw [hgb] at hgb'
    cases hgb'
    rw [hb2] at hbody''
    have := congrArg List.length hbody''
    simp at this
    omega
  subst hk''
  exact ⟨fb, gb, fr2, hst, ⟨hfb, hgb, hend, hR.invf, hinv2, by rw [hsl2]; exact hR.slots,
    hR.agreeF, hag2, hsite2, hR.facts, hR.factSites⟩⟩

/-- From the relation with `f` at the end of its body, `g` runs its pure tail. -/
theorem AtEnd.of_rel (H : Hyp f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = []) :
    ∃ fb gb fr2, LStar fr' m fr2 m ∧ AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m := by
  exact AtEnd.of_relT H.toT hrun hR hm hb

/-! ## Block entry -/

/-- **Block entry.** Both frames at the end of block `bi` (`AtEnd`) enter the same successor
with the same argument values: the frames are related at the start of the successor `si` with
its entry facts, at every memory `m'` agreeing with `m` where the edge keeps memory facts (a
branch: `m' = m`; after a `try_call`: any memory). -/
theorem rel_enterT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr' : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m)
    {bc bc' : BlockCall} {fr1 : Frame} (hbc : bc.block ∈ termSuccs fb.term)
    (hblk : bc'.block = bc.block)
    (hga : ∀ vs, fr.getMany bc.args = .ok vs → fr'.getMany bc'.args = .ok vs)
    (he : enterBlock fr bc = .ok fr1) :
    ∃ si fr1', (ccOf fi gi cert norm).index bc.block = some si ∧
      enterBlock fr' bc' = .ok fr1' ∧
      ∀ m' : Mem, (∀ F ∈ (if fb.term.isTry then kill S else S), F.isMem = true → m' = m) →
        Rel f g fi gi cert norm syms si 0 0 ((ccOf fi gi cert norm).factsAt si) fr1 fr1' m' := by
  obtain ⟨hT, hsucc⟩ := hE.endOk
  obtain ⟨si, hsi, hS⟩ := hsucc bc.block hbc
  obtain ⟨hb, hft⟩ := inv_end hE.invf hE.hfb
  obtain ⟨hb', hgt⟩ := inv_end hE.invg hE.hgb
  have hTS : termSuccs fb.term = termSuccs gb.term := by
    have := congrArg termSuccs hT
    rwa [termSuccs_mapTerm, termSuccs_mapTerm] at this
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := H.wff.inv_enter hE.invf hb (by rw [hft]; exact hbc) he
  obtain ⟨-, -, hid⟩ := H.wff.block?_index hb2
  have hjs : j = si := by
    have h1 := H.wff.ids j b2 hj
    rw [hid] at h1
    exact Option.some.inj (h1.symm.trans hsi)
  rw [hjs] at hj hinv1
  obtain ⟨b2x, args, regs, hb2x, hgaF, hty, hset, hfr1⟩ := enterBlock_ok he
  rw [hE.invf.func, hb2] at hb2x
  cases hb2x
  have hfr1f : fr1.func = fr.func := by subst hfr1; rfl
  have hfr1s : fr1.slots = fr.slots := by subst hfr1; rfl
  have hfr1r : fr1.regs = regs := by subst hfr1; rfl
  have hr1 : ∀ v, v ∉ b2.params.map (·.1) → fr1.regs v = fr.regs v := fun v hv => by
    rw [hfr1r]; exact ((setMany_spec hset).2 v).1 hv
  have hlt : si < g.blocks.length := by
    rw [H.ok.len]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨gb2, hj'⟩ : ∃ gb2, g.blocks[si]? = some gb2 := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hgb2 : g.block? bc.block = some gb2 := block?_gT H hb2 hj hj'
  obtain ⟨hentry, hbok⟩ := H.ok.blocks si b2 gb2 hj hj'
  have bok := blockOk_spec hbok
  have hgaG := hga args hgaF
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := gb2.params.map (·.1)) (vs := args)
    (by
      have h1 := (setMany_spec hset).1
      have h2 := congrArg List.length bok.paramTys
      simp only [List.length_map] at h1 h2 ⊢
      omega)
  have he' : enterBlock fr' bc' =
      .ok { fr' with regs := regs', body := gb2.body, term := gb2.term } :=
    enterBlock_of (by rw [hE.invg.func, hblk]; exact hgb2) hgaG (by rw [hty, bok.paramTys]) hset'
  have hsucc' : bc'.block ∈ termSuccs fr'.term := by
    rw [hgt, hblk, ← hTS]; exact hbc
  obtain ⟨jx, b3, hj3, hb3, hinv2⟩ := H.wfg.inv_enter hE.invg hb' hsucc' he'
  rw [hblk, hgb2] at hb3
  cases hb3
  have hjx : jx = si := H.wfg.idx_unique hj3 hj' rfl
  rw [hjx] at hinv2
  refine ⟨si, _, hsi, he', fun m' hm' => ?_⟩
  have hlen : b2.params.length = gb2.params.length := by
    have := congrArg List.length bok.paramTys
    simpa using this
  -- the values of `g` at the entry of `si`
  have hG : ∀ y, Avail (wfData g gi) si 0 y →
      TV f cert syms fr1 ((ccOf fi gi cert norm).eg y) =
        ({ fr' with regs := regs', body := gb2.body, term := gb2.term } : Frame).regs y ∧
      LeP fi.cfg.idom ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y)) (si, 0) := by
    intro y hy
    by_cases hdy : (wfData g gi).dm y = some (si, 0)
    · obtain ⟨b4, q, hb4, hq, hqy⟩ := H.wfg.site_param' hdy
      rw [hj'] at hb4
      cases hb4
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
      have hil : i < b2.params.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
      have hpi : b2.params[i]? = some b2.params[i] := List.getElem?_eq_getElem hil
      have htmg := bok.paramsG i q hi
      have hsiteG : (ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg y) = (si, 0) := by
        rw [← hqy]; exact CC.tmOk_atom (CC.tmsOk_get H.ok.tms htmg) rfl
      refine ⟨?_, by rw [hsiteG]; exact LeP.refl _ _⟩
      rw [← hqy, tv_param (cert := cert) (syms := syms) htmg hj hpi, hfr1r]
      show regs b2.params[i].1 = regs' q.1
      rw [setMany_param hset hpi (params_uniq (env := (ccOf fi gi cert norm).ef) bok.paramsF hpi),
        setMany_param hset' hi (params_uniq (env := (ccOf fi gi cert norm).eg) bok.paramsG hi)]
    · have hgsucc : gb2.id ∈ termSuccs gb.term := by
        rw [id_eqT H hj hj', hid, ← hTS]; exact hbc
      have hya := H.wfg.avail_pred hE.hgb hj' hgsucc hy hdy
      obtain ⟨d, t, hd, hva⟩ := hy
      rcases hva with ⟨hds, ht0⟩ | ⟨hne, ha⟩
      · exact absurd (by rw [hd, hds, show t = 0 by omega]) hdy
      have hnp : y ∉ gb2.params.map (·.1) := fun hm => by
        obtain ⟨q, hq, hqy⟩ := List.mem_map.1 hm
        exact hdy (by rw [← hqy]; exact H.wfg.site_param hj' hq)
      have ha2 : Anc fi.cfg.idom d si := by rw [← H.idomG]; exact ha
      have hanc := ancB_sound (H.ok.sitesG y d t (H.wfg.sitesRev y (d, t) hd))
      obtain ⟨hne', ha'⟩ := strict_of_ancT H hanc hne ha2
      refine ⟨?_, LeP.of_anc hne' ha' 0⟩
      rw [TV_enterT H (fr := fr) (fr1 := fr1) hfr1f hfr1s hj hr1 hne' ha']
      show _ = regs' y
      rw [((setMany_spec hset').2 y).1 hnp]
      exact hE.agreeG y hya
  refine ⟨⟨b2, gb2, ?_⟩, hinv1, hinv2, by rw [hfr1s]; exact hE.slots, ?_, fun y hy => (hG y hy).1,
    fun y hy => (hG y hy).2, ?_, ?_⟩
  · obtain ⟨Send, hw, hend⟩ := bok.walk
    exact ⟨Send, hj, hj', by simpa only [List.drop_zero] using hw, hend⟩
  · intro x hx
    by_cases hdx : (wfData f fi).dm x = some (si, 0)
    · obtain ⟨b4, p, hb4, hp, hpx⟩ := H.wff.site_param' hdx
      rw [hj] at hb4
      cases hb4
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
      rw [← hpx]
      exact tv_param (cert := cert) (syms := syms) (bok.paramsF i p hi) hj hi
    · have hxa := H.wff.avail_pred hE.hfb hj (by rw [hid]; exact hbc) hx hdx
      obtain ⟨d, t, hd, hva⟩ := hx
      rcases hva with ⟨hds, ht0⟩ | ⟨hne, ha⟩
      · exact absurd (by rw [hd, hds, show t = 0 by omega]) hdx
      have hnp : x ∉ b2.params.map (·.1) := fun hm => by
        obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hm
        exact hdx (by rw [← hpx]; exact H.wff.site_param hj hp)
      have hle := H.le_sound (H.ok.sitesF x (d, t) (H.wff.sitesRev x (d, t) hd))
      obtain ⟨hne', ha'⟩ := strict_of_leT H hle hne ha
      rw [TV_enterT H (fr := fr) (fr1 := fr1) hfr1f hfr1s hj hr1 hne' ha', hr1 x hnp]
      exact hE.agreeF x hxa
  · intro F hF
    have hFS := hS F hF
    have hFS' : F ∈ S := by
      split at hFS
      · exact (List.mem_filter.1 hFS).1
      · exact hFS
    refine factHolds_of_TV (fr1 := fr) (fr2 := fr1) (by rw [hfr1f]) (by rw [hfr1f]) hfr1s
      (fun t ht => ?_) (fun hmem => hm' F hFS hmem) (hE.facts F hFS')
    rcases entryOk_spec hentry F hF t ht with ⟨hne, ha⟩ | ⟨-, -, hcl⟩
    · exact TV_enterT H hfr1f hfr1s hj hr1 hne (ancB_sound ha)
    · exact TV_closed hfr1f hfr1s hcl
  · intro F hF t ht
    rcases entryOk_spec hentry F hF t ht with ⟨hne, ha⟩ | ⟨hsi, hs, -⟩
    · exact LeP.of_anc hne (ancB_sound ha) 0
    · rw [hs, hsi]
      exact LeP.refl _ _

/-- **Block entry.** Both frames at the end of block `bi` (`AtEnd`) enter the same successor
with the same argument values: the frames are related at the start of the successor `si` with
its entry facts, at every memory `m'` agreeing with `m` where the edge keeps memory facts (a
branch: `m' = m`; after a `try_call`: any memory). -/
theorem rel_enter (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr' : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr' m)
    {bc bc' : BlockCall} {fr1 : Frame} (hbc : bc.block ∈ termSuccs fb.term)
    (hblk : bc'.block = bc.block)
    (hga : ∀ vs, fr.getMany bc.args = .ok vs → fr'.getMany bc'.args = .ok vs)
    (he : enterBlock fr bc = .ok fr1) :
    ∃ si fr1', (ccOf fi gi cert norm).index bc.block = some si ∧
      enterBlock fr' bc' = .ok fr1' ∧
      ∀ m' : Mem, (∀ F ∈ (if fb.term.isTry then kill S else S), F.isMem = true → m' = m) →
        Rel f g fi gi cert norm syms si 0 0 ((ccOf fi gi cert norm).factsAt si) fr1 fr1' m' := by
  exact rel_enterT H.toT hE hbc hblk hga he

/-! ## Terminators -/

/-- The local steps of both frames at the end of a block agree. -/
theorem end_stepT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', lstep fr2 m = .next fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ vals, lstep fr m = .ret vals → lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals → lstep fr2 m = .tail ext vals) ∧
    (∀ c, lstep fr m = .trap c → lstep fr2 m = .trap c) := by
  obtain ⟨hb, hft⟩ := inv_end hE.invf hE.hfb
  obtain ⟨hb2, hgt⟩ := inv_end hE.invg hE.hgb
  refine term_step (Q := fun a b m1 => MR f g fi gi cert norm syms a b m1) hb hb2 hft hgt
    hE.endOk.1 (AtEnd.opsT H hE) (by rw [hE.invg.func, hE.invf.func, H.ok.externs])
    (by rw [hE.invg.func, hE.invf.func, H.ok.sig]) fun bc bc' fr1 hs hblk hga he => ?_
  obtain ⟨si, fr1', -, he', hrel⟩ := rel_enterT H hE hs hblk hga he
  exact ⟨fr1', he', si, 0, 0, _, hrel m fun _ _ _ => rfl⟩

/-- The local steps of both frames at the end of a block agree. -/
theorem end_step (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', lstep fr2 m = .next fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ vals, lstep fr m = .ret vals → lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals → lstep fr2 m = .tail ext vals) ∧
    (∀ c, lstep fr m = .trap c → lstep fr2 m = .trap c) := by
  exact end_stepT H.toT hE

/-- **The terminators.** -/
theorem rel_termT (H : HypT f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = []) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ vals, lstep fr m = .ret vals → ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals →
      ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .tail ext vals) ∧
    (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') := by
  obtain ⟨fb, gb, fr2, hst, hE⟩ := AtEnd.of_relT H hrun hR hm hb
  obtain ⟨h1, h2, h3, h4⟩ := end_stepT H hE
  refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ⟨fr2, hst, h2 vals hl⟩,
    fun ext vals hl => ⟨fr2, hst, h3 ext vals hl⟩, fun c hl => ⟨fr2, m, hst, h4 c hl⟩⟩
  obtain ⟨fr1', hl', hq⟩ := h1 fr1 m1 hl
  exact ⟨fr1', hst.trans (.step hl' (.refl _ _)), hq⟩

/-- **The terminators.** -/
theorem rel_term (H : Hyp f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm)
    {bi k k' : Nat} {S : List Fact} {fr fr' : Frame} {m : Mem}
    (hR : Rel f g fi gi cert norm syms bi k k' S fr fr' m) (hm : m.symbols = syms)
    (hb : fr.body = []) :
    (∀ fr1 m1, lstep fr m = .next fr1 m1 →
      ∃ fr1', LStar fr' m fr1' m1 ∧ MR f g fi gi cert norm syms fr1 fr1' m1) ∧
    (∀ vals, lstep fr m = .ret vals → ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .ret vals) ∧
    (∀ ext vals, lstep fr m = .tail ext vals →
      ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .tail ext vals) ∧
    (∀ c', lstep fr m = .trap c' → ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c') := by
  exact rel_termT H.toT hrun hR hm hb

/-! ## `try_call` -/

/-- The successor arguments of a `try_call` read alike once both frames bind the same values
at their fresh values. -/
theorem pair_regsT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) {n : Nat} {vs : List Val} {r r' : Regs}
    (h : fr.regs.setMany (tryRets n fr.func.freshValue) vs = some r)
    (h' : fr2.regs.setMany (tryRets n fr2.func.freshValue) vs = some r') :
    ∀ x y, ((∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧ x = v ∧ y = w ∧
        (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) →
      ({ fr2 with regs := r' } : Frame).regs y = ({ fr with regs := r } : Frame).regs x := by
  intro x y hq
  rcases hq with ⟨v, w, hv, hw', h1, h2, hvw⟩ | ⟨i, rfl, rfl⟩
  · rw [h1, h2]
    show r' w = r v
    rw [set_lo hE.invg.func h' w (H.wfg.avail_lt (H.wfg.termUses bi gb hE.hgb w hw')),
      set_lo hE.invf.func h v (H.wff.avail_lt (H.wff.termUses bi fb hE.hfb v hv))]
    exact AtEnd.opsT H hE v hv w hw' hvw
  · show r' (fr2.func.freshValue + i) = r (fr.func.freshValue + i)
    rw [setMany_tryRets h' i, setMany_tryRets h i]
    split
    · rfl
    · exact (hw i).symm

/-- The successor arguments of a `try_call` read alike once both frames bind the same values
at their fresh values. -/
theorem pair_regs (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) {n : Nat} {vs : List Val} {r r' : Regs}
    (h : fr.regs.setMany (tryRets n fr.func.freshValue) vs = some r)
    (h' : fr2.regs.setMany (tryRets n fr2.func.freshValue) vs = some r') :
    ∀ x y, ((∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧ x = v ∧ y = w ∧
        (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) →
      ({ fr2 with regs := r' } : Frame).regs y = ({ fr with regs := r } : Frame).regs x := by
  exact pair_regsT H.toT hE hw h h'

/-- The normal-return edge of a `try_call`. -/
theorem tcontT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) (hTry : fb.term.isTry = true) {n : Nat} {bc bc2 : BlockCall}
    (hsucc : bc.block ∈ termSuccs fb.term) (hblk : bc2.block = bc.block)
    (hpw : Pw2 (fun x y => (∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧
        x = v ∧ y = w ∧ (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) bc.args bc2.args)
    (rtys : List Ty) :
    TContM syms (MRW f g fi gi cert norm syms) fr (tryRets n fr.func.freshValue) bc fr2
      (tryRets n fr2.func.freshValue) bc2 rtys := by
  intro vs regs m1 _ _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr2.regs) (xs := tryRets n fr2.func.freshValue)
    (vs := vs) (by have := (setMany_spec hset).1; simpa [tryRets] using this)
  refine ⟨regs', hset', fun fr1 he => ?_⟩
  have hE' := AtEnd.regs_congrT H hE (set_lo hE.invf.func hset) (set_lo hE.invg.func hset')
  obtain ⟨si, fr1', -, he', hrel⟩ := rel_enterT H hE' hsucc hblk
    (fun vs' hv => getMany_pw2 (hpw.imp (pair_regsT H hE hw hset hset')) hv) he
  exact ⟨fr1', he', ⟨si, 0, 0, _, hrel m1 (nomem hTry)⟩, win_enter he he' (win_set hw hset hset')⟩

/-- The normal-return edge of a `try_call`. -/
theorem tcont (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) (hTry : fb.term.isTry = true) {n : Nat} {bc bc2 : BlockCall}
    (hsucc : bc.block ∈ termSuccs fb.term) (hblk : bc2.block = bc.block)
    (hpw : Pw2 (fun x y => (∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧
        x = v ∧ y = w ∧ (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) bc.args bc2.args)
    (rtys : List Ty) :
    TContM syms (MRW f g fi gi cert norm syms) fr (tryRets n fr.func.freshValue) bc fr2
      (tryRets n fr2.func.freshValue) bc2 rtys := by
  exact tcontT H.toT hE hw hTry hsucc hblk hpw rtys

/-- The handler edges of a `try_call`. -/
theorem hcontT (H : HypT f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) (hTry : fb.term.isTry = true) {et et' : ExnTable}
    (het : et.mapVals (ccOf fi gi cert norm).ef = et'.mapVals (ccOf fi gi cert norm).eg)
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fb.term)
    (hvf : ∀ d ∈ et.handlers, ∀ v ∈ d.vals, v ∈ termOperands fb.term)
    (hvg : ∀ d ∈ et'.handlers, ∀ w ∈ d.vals, w ∈ termOperands gb.term) :
    HContM syms (MRW f g fi gi cert norm syms) fr et fr2 et' := by
  intro e
  have hcatch : (et.catch? e).map (·.mapVals (ccOf fi gi cert norm).ef) =
      (et'.catch? e).map (·.mapVals (ccOf fi gi cert norm).eg) := by
    rw [← catch?_mapVals, ← catch?_mapVals, het]
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢
    rw [hn] at hcatch
    cases h' : et'.catch? e with
    | none => rfl
    | some d' => rw [h'] at hcatch; cases hcatch
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    rw [hd] at hcatch
    cases hd' : et'.catch? e with
    | none => rw [hd'] at hcatch; cases hcatch
    | some d' =>
      rw [hd'] at hcatch
      have hdd : d.mapVals (ccOf fi gi cert norm).ef = d'.mapVals (ccOf fi gi cert norm).eg :=
        Option.some.inj hcatch
      obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryHandler_pair2 hdd (b2 := fr2.func.freshValue) hbc
      obtain ⟨regs', hset'⟩ := setMany_len (r := fr2.regs)
        (xs := (List.range e.payload.length).map (fr2.func.freshValue + ·)) (vs := e.payload)
        (by simp)
      refine ⟨_, catchIn_of hd' hbc2 hset', rfl, rfl, bc, bc2, rfl, rfl, fun a1 he1 => ?_⟩
      have he1' : enterBlock { fr with regs := regs } bc = .ok a1 := by
        rw [← enterBlock_bt { fr with regs := regs } [] (.jump bc)]; exact he1
      have hset0 : fr.regs.setMany (tryRets e.payload.length fr.func.freshValue) e.payload =
          some regs := hset
      have hset0' : fr2.regs.setMany (tryRets e.payload.length fr2.func.freshValue) e.payload =
          some regs' := hset'
      have hE' := AtEnd.regs_congrT H hE (set_lo hE.invf.func hset0) (set_lo hE.invg.func hset0')
      have hpw' : Pw2 (fun x y => ({ fr2 with regs := regs' } : Frame).regs y =
          ({ fr with regs := regs } : Frame).regs x) bc.args bc2.args :=
        hpw.imp fun x y hq => pair_regsT H hE hw hset0 hset0' x y (by
          rcases hq with ⟨v, w, hv, hw', h1, h2, h3⟩ | hq
          · exact .inl ⟨v, w, hvf d (catch?_mem hd) v hv, hvg d' (catch?_mem hd') w hw', h1, h2, h3⟩
          · exact .inr hq)
      have hsb : bc.block ∈ termSuccs fb.term := by
        rw [tryHandler_block hbc]; exact hsucc d (catch?_mem hd)
      obtain ⟨si, fr1', -, he', hrel⟩ :=
        rel_enterT H hE' hsb hblk (fun vs hv => getMany_pw2 hpw' hv) he1'
      exact ⟨fr1', (enterBlock_bt { fr2 with regs := regs' } [] (.jump bc2) bc2).trans he',
        fun m1 _ => ⟨⟨si, 0, 0, _, hrel m1 (nomem hTry)⟩,
          win_enter he1' he' (win_set hw hset0 hset0')⟩⟩

/-- The handler edges of a `try_call`. -/
theorem hcont (H : Hyp f g fi gi cert norm) {bi : Nat} {fb gb : Block} {S : List Fact}
    {fr fr2 : Frame} {m : Mem} (hE : AtEnd f g fi gi cert norm syms bi fb gb S fr fr2 m)
    (hw : Win fr fr2) (hTry : fb.term.isTry = true) {et et' : ExnTable}
    (het : et.mapVals (ccOf fi gi cert norm).ef = et'.mapVals (ccOf fi gi cert norm).eg)
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fb.term)
    (hvf : ∀ d ∈ et.handlers, ∀ v ∈ d.vals, v ∈ termOperands fb.term)
    (hvg : ∀ d ∈ et'.handlers, ∀ w ∈ d.vals, w ∈ termOperands gb.term) :
    HContM syms (MRW f g fi gi cert norm syms) fr et fr2 et' := by
  exact hcontT H.toT hE hw hTry het hsucc hvf hvg

/-- **`try_call` and `try_call_indirect`** (with equal windows, `MRW`). -/
theorem rel_tryT (H : HypT f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm) :
    TryOkMU syms (MRW f g fi gi cert norm syms) where
  call := by
    intro fr fr' m fn args et n base bc ext vals hR hm hb ht htc hca
    obtain ⟨⟨bi, k, k', S, hR⟩, hw⟩ := hR
    obtain ⟨fb, gb, fr2, hst, hE⟩ := AtEnd.of_relT H hrun hR hm hb
    obtain ⟨-, hft⟩ := inv_end hE.invf hE.hfb
    obtain ⟨hb2, hgt⟩ := inv_end hE.invg hE.hgb
    have hfb : fb.term = .tryCall fn args et := hft.symm.trans ht
    have hT := hE.endOk.1
    rw [hfb] at hT
    obtain ⟨args', et', hgb, hargs, het⟩ : ∃ args' et', gb.term = .tryCall fn args' et' ∧
        args.map (ccOf fi gi cert norm).ef = args'.map (ccOf fi gi cert norm).eg ∧
        et.mapVals (ccOf fi gi cert norm).ef = et'.mapVals (ccOf fi gi cert norm).eg := by
      cases hg : gb.term <;> rw [hg] at hT <;>
        simp only [mapTerm, reduceCtorEq, Terminator.tryCall.injEq] at hT
      obtain ⟨rfl, h2, h3⟩ := hT
      exact ⟨_, _, rfl, h2, h3⟩
    have hw2 : Win fr fr2 := by
      obtain ⟨-, hf2, hw2⟩ := LStar.win (inB_of_inv hR.invg) hst
      intro i
      rw [hf2, hw2 i]
      exact hw i
    have hops := AtEnd.opsT H hE
    rw [hfb, hgb] at hops
    have hf : fr.func = f := hE.invf.func
    have hg2 : fr2.func = g := hE.invg.func
    obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair2 (σf := (ccOf fi gi cert norm).ef)
      (σg := (ccOf fi gi cert norm).eg) (et := et) (et' := et') (congrArg ExnTable.normal het)
      (b2 := fr2.func.freshValue) hbc
    have hsig : et'.sig = et.sig := (congrArg ExnTable.sig het).symm
    have htc2 : tcArgs fr2 fn et' = .ok (e0.sig.returns.length, fr2.func.freshValue, bc2) := by
      refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc2, rfl⟩
      · rw [hg2]
        rw [hf] at he0
        simp only [Function.extern?, H.ok.externs] at he0 ⊢
        exact he0
      · rw [hg2, H.ok.sigDecls, hsig]
        rw [hf] at hs0
        exact hs0
    have hpwa : Pw2 (fun x y => fr2.regs y = fr.regs x) args args' :=
      pw2_of_map hargs fun x hx y hy hxy =>
        hops x (by simp [termOperands, hx]) y (by simp [termOperands, hy]) hxy
    have hca2 : callArgs fr2 fn args' = .ok (ext, vals) :=
      Res.norm_eq_ok (callArgs_pw (by rw [hg2, hf, H.ok.externs]) hpwa) hca
    have hpw' : Pw2 (fun x y => (∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧
        x = v ∧ y = w ∧ (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) bc.args bc2.args :=
      hpw.imp fun x y hq => by
        rcases hq with ⟨v, w, hv, hw', h1, h2, h3⟩ | hq
        · exact .inl ⟨v, w, by rw [hfb]; exact normal_vals_sub v hv,
            by rw [hgb]; exact normal_vals_sub w hw', h1, h2, h3⟩
        · exact .inr hq
    have hTry : fb.term.isTry = true := by simp only [hfb, Terminator.isTry]
    refine ⟨fr2, fn, args', et', fr2.func.freshValue, bc2, hst, hb2, hgt.trans hgb, htc2, hca2,
      tcontT H hE hw2 hTry (by rw [hfb]; exact normal_succ hbc) hblk hpw' _, ?_⟩
    exact hcontT H hE hw2 hTry het (fun d hd => by rw [hfb]; exact handler_succ hd)
      (fun d hd v hv => by rw [hfb]; simp [termOperands, handler_vals hd hv])
      (fun d hd w hw' => by rw [hgb]; simp [termOperands, handler_vals hd hw'])
  ind := by
    intro fr fr' m callee args et n base bc dsig a vals hR hm hb ht htc hca
    obtain ⟨⟨bi, k, k', S, hR⟩, hw⟩ := hR
    obtain ⟨fb, gb, fr2, hst, hE⟩ := AtEnd.of_relT H hrun hR hm hb
    obtain ⟨-, hft⟩ := inv_end hE.invf hE.hfb
    obtain ⟨hb2, hgt⟩ := inv_end hE.invg hE.hgb
    have hfb : fb.term = .tryCallIndirect callee args et := hft.symm.trans ht
    have hT := hE.endOk.1
    rw [hfb] at hT
    obtain ⟨callee', args', et', hgb, hc, hargs, het⟩ : ∃ callee' args' et',
        gb.term = .tryCallIndirect callee' args' et' ∧
        (ccOf fi gi cert norm).ef callee = (ccOf fi gi cert norm).eg callee' ∧
        args.map (ccOf fi gi cert norm).ef = args'.map (ccOf fi gi cert norm).eg ∧
        et.mapVals (ccOf fi gi cert norm).ef = et'.mapVals (ccOf fi gi cert norm).eg := by
      cases hg : gb.term <;> rw [hg] at hT <;>
        simp only [mapTerm, reduceCtorEq, Terminator.tryCallIndirect.injEq] at hT
      obtain ⟨h1, h2, h3⟩ := hT
      exact ⟨_, _, _, rfl, h1, h2, h3⟩
    have hw2 : Win fr fr2 := by
      obtain ⟨-, hf2, hw2⟩ := LStar.win (inB_of_inv hR.invg) hst
      intro i
      rw [hf2, hw2 i]
      exact hw i
    have hops := AtEnd.opsT H hE
    rw [hfb, hgb] at hops
    have hf : fr.func = f := hE.invf.func
    have hg2 : fr2.func = g := hE.invg.func
    obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair2 (σf := (ccOf fi gi cert norm).ef)
      (σg := (ccOf fi gi cert norm).eg) (et := et) (et' := et') (congrArg ExnTable.normal het)
      (b2 := fr2.func.freshValue) hbc
    have hsig : et'.sig = et.sig := (congrArg ExnTable.sig het).symm
    have htc2 : ticArgs fr2 et' = .ok (s0.returns.length, fr2.func.freshValue, bc2) := by
      refine ticArgs_ok.2 ⟨s0, ?_, rfl, hbc2, rfl⟩
      rw [hg2, H.ok.sigDecls, hsig]
      rw [hf] at hs0
      exact hs0
    have hpwa : Pw2 (fun x y => fr2.regs y = fr.regs x) args args' :=
      pw2_of_map hargs fun x hx y hy hxy =>
        hops x (by simp [termOperands, hx]) y (by simp [termOperands, hy]) hxy
    have hca2 : ciArgs fr2 et'.sig callee' args' = .ok (dsig, a, vals) := by
      rw [hsig]
      exact ciArgs_pw (by rw [hg2, hf, H.ok.sigDecls])
        (hops callee (by simp [termOperands]) callee' (by simp [termOperands]) hc) hpwa hca
    have hpw' : Pw2 (fun x y => (∃ v w, v ∈ termOperands fb.term ∧ w ∈ termOperands gb.term ∧
        x = v ∧ y = w ∧ (ccOf fi gi cert norm).ef v = (ccOf fi gi cert norm).eg w) ∨
        ∃ i, x = fr.func.freshValue + i ∧ y = fr2.func.freshValue + i) bc.args bc2.args :=
      hpw.imp fun x y hq => by
        rcases hq with ⟨v, w, hv, hw', h1, h2, h3⟩ | hq
        · exact .inl ⟨v, w, by rw [hfb]; exact normal_vals_sub' v hv,
            by rw [hgb]; exact normal_vals_sub' w hw', h1, h2, h3⟩
        · exact .inr hq
    have hTry : fb.term.isTry = true := by simp only [hfb, Terminator.isTry]
    refine ⟨fr2, callee', args', et', fr2.func.freshValue, bc2, hst, hb2, hgt.trans hgb, htc2, hca2,
      tcontT H hE hw2 hTry (by rw [hfb]; exact normal_succ hbc) hblk hpw' _, ?_⟩
    exact hcontT H hE hw2 hTry het (fun d hd => by rw [hfb]; exact handler_succ hd)
      (fun d hd v hv => by rw [hfb]; simp [termOperands, handler_vals hd hv])
      (fun d hd w hw' => by rw [hgb]; simp [termOperands, handler_vals hd hw'])

/-- **`try_call` and `try_call_indirect`** (with equal windows, `MRW`). -/
theorem rel_try (H : Hyp f g fi gi cert norm) (hrun : GPreRun f g fi gi cert norm) :
    TryOkMU syms (MRW f g fi gi cert norm syms) where
  call := (rel_tryT H.toT hrun).call
  ind := (rel_tryT H.toT hrun).ind

end

end Opt.MidVal

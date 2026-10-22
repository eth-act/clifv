import FV.Opt.Proof.UnreachableX
import FV.Opt.Retype

/-!
# The retyping refines (S12e, #36)

`Opt.Retype.retype_simX`: on its domain (`okB`), `retype σ f` simulates `f`, `call_indirect`
and `try_call`/`try_call_indirect` included (`Opt.FunSimX`, lifted to programs by
`Opt.runLoop_refinesX`). A frame of `f` and a frame of `retype σ f` are related (`RR`) at the
same program point (the target's statements retyped) when their registers agree outside the
values of the retyped loads (`vals σ f`) and hold the `retag`ged value at those. Each local step
is matched by one step: a retyped load defines the retagged value, a retyped store reads it
and writes the same bytes, every other statement and terminator reads equal registers and
binds outside `vals σ f`.
-/

namespace Opt.Retype

open Clif Opt

variable {σ : TyMap}

/-! ## The retyped function -/

theorem retypeBlock_id (b : Block) : (retypeBlock σ b).id = b.id := rfl
theorem retypeBlock_params (b : Block) : (retypeBlock σ b).params = b.params := rfl
theorem retypeBlock_term (b : Block) : (retypeBlock σ b).term = b.term := rfl
theorem retypeBlock_body (b : Block) : (retypeBlock σ b).body = b.body.map (retypeStmt σ) := rfl

theorem retype_block? (f : Function) (id : BlockId) :
    (retype σ f).block? id = (f.block? id).map (retypeBlock σ) := by
  simp only [Function.block?, retype, List.find?_map]
  rfl

theorem retype_entry? (f : Function) :
    (retype σ f).entry? = f.entry?.map (retypeBlock σ) := by
  simp only [Function.entry?, retype, List.head?_map]

theorem retype_freshValue (f : Function) : (retype σ f).freshValue = f.freshValue := by
  simp only [Function.freshValue, retype, List.foldl_map, retypeBlock_params, retypeBlock_body,
    retypeStmt]

theorem retypeInst_call {i : Inst} {fn : FnRef} {args : List ValueId} :
    retypeInst σ i = .call fn args ↔ i = .call fn args := by
  cases i <;> simp only [retypeInst, reduceCtorEq] <;> (try split) <;> simp_all

theorem retypeInst_callIndirect {i : Inst} {sig : Nat} {c : ValueId} {args : List ValueId} :
    retypeInst σ i = .callIndirect sig c args ↔ i = .callIndirect sig c args := by
  cases i <;> simp only [retypeInst, reduceCtorEq] <;> (try split) <;> simp_all

theorem retypeInst_other {i : Inst} (h1 : isRLoad σ i = false) (h2 : isRStore σ i = false) :
    retypeInst σ i = i := by
  cases i <;> simp only [retypeInst] <;> try rfl
  · rename_i op t fl p off
    cases op <;> simp_all [isRLoad]
  · rename_i op t fl x p off
    cases op <;> simp_all [isRStore]

theorem isRLoad_spec {i : Inst} (h : isRLoad σ i = true) :
    ∃ t t' fl p off, i = .load .load t fl p off ∧ σ.map t = some t' ∧
      retypeInst σ i = .load .load t' fl p off := by
  cases i <;> simp only [isRLoad, reduceCtorEq] at h
  rename_i op t fl p off
  cases op <;> simp only [Option.isSome_iff_exists, Bool.false_eq_true] at h
  obtain ⟨t', ht⟩ := h
  exact ⟨t, t', fl, p, off, rfl, ht, by simp [retypeInst, ht]⟩

theorem isRStore_spec {i : Inst} (h : isRStore σ i = true) :
    ∃ t t' fl x p off, i = .store .store t fl x p off ∧ σ.map t = some t' ∧
      retypeInst σ i = .store .store t' fl x p off := by
  cases i <;> simp only [isRStore, reduceCtorEq] at h
  rename_i op t fl x p off
  cases op <;> simp only [Option.isSome_iff_exists, Bool.false_eq_true] at h
  obtain ⟨t', ht⟩ := h
  exact ⟨t, t', fl, x, p, off, rfl, ht, by simp [retypeInst, ht]⟩

/-! ## Retagged values -/

theorem retag_of {t t' : Ty} (ht : σ.map t = some t') (b : BitVec t.width) :
    retag σ ⟨t, b⟩ = ⟨t', b.cast (σ.width _ _ ht).symm⟩ := by
  unfold retag
  split
  · rename_i t2 h2
    simp only at h2
    rw [ht] at h2
    cases h2
    rfl
  · rename_i h2
    simp only at h2
    rw [ht] at h2
    cases h2

theorem bytes_eq {t t' : Ty} (ht : σ.map t = some t') : t'.bytes = t.bytes := by
  simp only [Ty.bytes, σ.width _ _ ht]

theorem setWidth_cast {k w w' : Nat} (h : w = w') (x : BitVec k) :
    (x.zeroExtend w).cast h = x.zeroExtend w' := by
  subst h; rfl

theorem Mem.store_cast {m : Mem} {fl : MemFlags} {a n : Nat} {w w' : Nat} (h : w = w')
    (x : BitVec w) : m.store fl a n (x.cast h) = m.store fl a n x := by
  subst h; rfl

theorem as?_retag {t t' : Ty} (ht : σ.map t = some t') {v : Val} {a : BitVec t.width}
    (hv : v.as? t = some a) : (retag σ v).as? t' = some (a.cast (σ.width _ _ ht).symm) := by
  obtain ⟨vt, vb⟩ := v
  simp only [Val.as?] at hv
  split at hv
  · rename_i he
    subst he
    cases hv
    rw [retag_of ht]
    exact Val.as?_mk _ _
  · cases hv

/-! ## The retyped accesses -/

theorem evalInst_rload {fr fr' : Frame} {m : Mem} {t t' : Ty} {fl : MemFlags} {p : ValueId}
    {off : Int} (ht : σ.map t = some t') (hp : fr'.regs p = fr.regs p) :
    (∀ vs m', evalInst fr m (.load .load t fl p off) = .ok (vs, m') →
      evalInst fr' m (.load .load t' fl p off) = .ok (vs.map (retag σ), m')) ∧
    (∀ c, evalInst fr m (.load .load t fl p off) = .trap c →
      evalInst fr' m (.load .load t' fl p off) = .trap c) := by
  have hb := bytes_eq ht
  have hg : fr'.get p = fr.get p := by simp only [Frame.get, hp]
  simp only [evalInst, LoadOp.size, LoadOp.signed, hg, hb]
  cases hgp : fr.get p with
  | trap c => simp
  | stuck msg => simp
  | ok pv =>
    cases hl : m.load fl (effAddr pv off) t.bytes (8 * t.bytes) with
    | trap c => simp only [Res.ok_bind]; rw [hb, hl]; simp
    | stuck msg => simp only [Res.ok_bind]; rw [hb, hl]; simp
    | ok raw =>
      refine ⟨fun vs m' h => ?_, fun c h => ?_⟩
      · simp only [Res.ok_bind, hl, Nat.le_refl, decide_true, Res.check_true,
          Bool.false_eq_true, ite_false, pure] at h ⊢
        rw [hb, hl]
        simp only [Res.ok_bind, Res.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, rfl⟩
        rw [List.map_singleton, retag_of ht, setWidth_cast]
      · simp [hl] at h

theorem evalInst_rstore {fr fr' : Frame} {m : Mem} {t t' : Ty} {fl : MemFlags} {x p : ValueId}
    {off : Int} (ht : σ.map t = some t') (hp : fr'.regs p = fr.regs p)
    (hx : fr'.regs x = (fr.regs x).map (retag σ)) :
    (∀ vs m', evalInst fr m (.store .store t fl x p off) = .ok (vs, m') →
      evalInst fr' m (.store .store t' fl x p off) = .ok (vs, m')) ∧
    (∀ c, evalInst fr m (.store .store t fl x p off) = .trap c →
      evalInst fr' m (.store .store t' fl x p off) = .trap c) := by
  have hb := bytes_eq ht
  have hg : fr'.get p = fr.get p := by simp only [Frame.get, hp]
  cases hx0 : fr.regs x with
  | none =>
    have : fr.getAs x t = .stuck s!"use of undefined value v{x}" := by
      simp [Frame.getAs, Frame.get, hx0, Res.ofOption]
    simp [evalInst, this]
  | some v =>
    cases hv : v.as? t with
    | none =>
      have : ∃ msg, fr.getAs x t = .stuck msg := by
        simp [Frame.getAs, Frame.get, hx0, Res.ofOption, hv]
      obtain ⟨msg, hm⟩ := this
      simp [evalInst, hm]
    | some a =>
      have h1 : fr.getAs x t = .ok a := by
        simp [Frame.getAs, Frame.get, hx0, Res.ofOption, hv]
      have h2 : fr'.getAs x t' = .ok (a.cast (σ.width _ _ ht).symm) := by
        simp [Frame.getAs, Frame.get, hx, hx0, Res.ofOption, as?_retag ht hv]
      simp only [evalInst, StoreOp.size, h1, h2, hg, hb, Res.ok_bind, Mem.store_cast]
      exact ⟨fun _ _ h => h, fun _ h => h⟩

/-! ## The domain -/

theorem okB_block {f : Function} (h : okB σ f = true) {b : Block} (hb : b ∈ f.blocks) :
    (∀ p ∈ b.params, p.1 ∉ vals σ f) ∧ (∀ st ∈ b.body, stmtOkB σ (vals σ f) st = true) ∧
      ∀ v ∈ termOperands b.term, v ∉ vals σ f := by
  simp only [okB, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h b hb
  refine ⟨fun p hp => ?_, h2, fun v hv => ?_⟩
  · simpa using h1 p hp
  · simpa using h3 v hv

theorem stmtOk_rload {V : List ValueId} {st : Stmt} (h : stmtOkB σ V st = true)
    (hl : isRLoad σ st.inst = true) :
    st.results.length = 1 ∧ ∀ v ∈ operands st.inst, v ∉ V := by
  simp only [stmtOkB, hl, ite_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun v hv => by simpa using h.2 v hv⟩

theorem stmtOk_rstore {V : List ValueId} {st : Stmt} (h : stmtOkB σ V st = true)
    (hl : isRLoad σ st.inst = false) (hs : isRStore σ st.inst = true) :
    ∃ t fl x p off, st.inst = .store .store t fl x p off ∧ x ∈ V ∧ p ∉ V ∧ st.results = [] := by
  obtain ⟨t, t', fl, x, p, off, he, ht, -⟩ := isRStore_spec hs
  unfold stmtOkB at h
  rw [he] at hl hs h
  simp only [hl, hs, Bool.false_eq_true, ite_false, ite_true, Bool.and_eq_true] at h
  refine ⟨t, fl, x, p, off, he, by simpa using h.1.1, by simpa using h.1.2, by simpa using h.2⟩

theorem stmtOk_other {V : List ValueId} {st : Stmt} (h : stmtOkB σ V st = true)
    (hl : isRLoad σ st.inst = false) (hs : isRStore σ st.inst = false) :
    (∀ v ∈ operands st.inst, v ∉ V) ∧ ∀ r ∈ st.results, r ∉ V := by
  simp only [stmtOkB, hl, hs, Bool.false_eq_true, ite_false, Bool.and_eq_true,
    List.all_eq_true] at h
  exact ⟨fun v hv => by simpa using h.1 v hv, fun v hv => by simpa using h.2 v hv⟩

theorem mem_vals {f : Function} {b : Block} (hb : b ∈ f.blocks) {st : Stmt} (hst : st ∈ b.body)
    (hl : isRLoad σ st.inst = true) : ∀ r ∈ st.results, r ∈ vals σ f := by
  intro r hr
  simp only [vals, List.mem_flatMap]
  exact ⟨b, hb, st, hst, by simp [hl, hr]⟩

theorem vals_lt {f : Function} {v : ValueId} (hv : v ∈ vals σ f) : v < f.freshValue := by
  simp only [vals, List.mem_flatMap] at hv
  obtain ⟨b, hb, st, hst, hv⟩ := hv
  split at hv
  · exact (lt_freshValue hb).2 st hst v hv
  · cases hv

/-! ## Registers -/

/-- The register relation: equal outside `V`, retagged at `V`. -/
def RegRel (σ : TyMap) (V : List ValueId) (r r' : Regs) : Prop :=
  Agree (fun v => v ∉ V) r r' ∧ ∀ v ∈ V, r' v = (r v).map (retag σ)

theorem RegRel.get {V : List ValueId} {r r' : Regs} (h : RegRel σ V r r') {v : ValueId}
    (hv : v ∉ V) : r' v = r v := h.1 v hv

/-- Binding values outside `V` keeps the relation. -/
theorem RegRel.setMany {V : List ValueId} {r r' r1 : Regs} (h : RegRel σ V r r')
    {xs : List ValueId} {vs : List Val} (hx : ∀ x ∈ xs, x ∉ V) (h1 : r.setMany xs vs = some r1) :
    ∃ r1', r'.setMany xs vs = some r1' ∧ RegRel σ V r1 r1' := by
  obtain ⟨r1', h1', hag⟩ := setMany_agree h.1 h1
  refine ⟨r1', h1', hag, fun v hv => ?_⟩
  have hn : v ∉ xs := fun hm => hx v hm hv
  rw [((setMany_spec h1').2 v).1 hn, ((setMany_spec h1).2 v).1 hn]
  exact h.2 v hv

/-- Binding a value of `V` to the retagged value keeps the relation. -/
theorem RegRel.set1 {V : List ValueId} {r r' r1 : Regs} (h : RegRel σ V r r')
    {x : ValueId} (hx : x ∈ V) {vs : List Val} (h1 : r.setMany [x] vs = some r1) :
    ∃ r1', r'.setMany [x] (vs.map (retag σ)) = some r1' ∧ RegRel σ V r1 r1' := by
  match vs, h1 with
  | [a], h1 =>
    simp only [Regs.setMany_cons, Regs.setMany_nil, Option.some.injEq] at h1
    subst h1
    refine ⟨r'.set x (retag σ a), rfl, fun v hv => ?_, fun v hv => ?_⟩
    · have : v ≠ x := fun he => hv (he ▸ hx)
      simp only [Regs.set_other _ _ this]
      exact h.1 v hv
    · by_cases he : v = x
      · subst he; simp
      · simp only [Regs.set_other _ _ he]; exact h.2 v hv

theorem RegRel.getMany {V : List ValueId} {fr fr' : Frame} (h : RegRel σ V fr.regs fr'.regs)
    {xs : List ValueId} (hx : ∀ x ∈ xs, x ∉ V) : fr'.getMany xs = fr.getMany xs :=
  getMany_congr fun x hm => h.1 x (hx x hm)

theorem RegRel.frameGet {V : List ValueId} {fr fr' : Frame} (h : RegRel σ V fr.regs fr'.regs)
    {x : ValueId} (hx : x ∉ V) : fr'.get x = fr.get x := by
  simp only [Frame.get, h.1 x hx]

/-! ## The relation -/

/-- A frame of `f` and a frame of `retype σ f` at the same program point (the target's
statements retyped), the registers related by `RegRel` (module doc). -/
def RR (σ : TyMap) (f : Function) (fr fr' : Frame) : Prop :=
  fr.func = f ∧ fr'.func = retype σ f ∧ fr'.slots = fr.slots ∧
    fr'.body = fr.body.map (retypeStmt σ) ∧ fr'.term = fr.term ∧
    (∃ b ∈ f.blocks, fr.body <:+ b.body ∧ fr.term = b.term) ∧
    RegRel σ (vals σ f) fr.regs fr'.regs

/-- Entering a block whose arguments are outside `vals σ f`. -/
theorem enterBlock_rr {f : Function} (hok : okB σ f = true) {X Y : Frame} (hf : X.func = f)
    (hg : Y.func = retype σ f) (hsl : Y.slots = X.slots)
    (hr : RegRel σ (vals σ f) X.regs Y.regs) {bc : BlockCall}
    (hbc : ∀ v ∈ bc.args, v ∉ vals σ f) {X1 : Frame} (h : enterBlock X bc = .ok X1) :
    ∃ Y1, enterBlock Y bc = .ok Y1 ∧ RR σ f X1 Y1 := by
  obtain ⟨b, args, regs, hb, hga, hty, hset, rfl⟩ := enterBlock_ok h
  rw [hf] at hb
  have hbm : b ∈ f.blocks := List.mem_of_find?_eq_some hb
  obtain ⟨hp, -, -⟩ := okB_block hok hbm
  obtain ⟨r', hset', hrr⟩ := hr.setMany (fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx; exact hp q hq) hset
  have hgb : Y.func.block? bc.block = some (retypeBlock σ b) := by
    rw [hg, retype_block?, hb]; rfl
  refine ⟨_, enterBlock_of hgb (by rw [hr.getMany hbc]; exact hga) hty hset', hf, hg, hsl, rfl, rfl,
    ⟨b, hbm, List.suffix_refl _, rfl⟩, hrr⟩

/-- A non-call statement whose evaluation and result binding are matched. -/
theorem lstep_inst_rel {fr fr' : Frame} {m : Mem} {st st' : Stmt} {rest rest' : List Stmt}
    (hb : fr.body = st :: rest) (hb' : fr'.body = st' :: rest')
    (hc : ∀ fn args, st.inst ≠ .call fn args) (hc' : ∀ fn args, st'.inst ≠ .call fn args)
    (g : List Val → List Val) (P : Frame → Frame → Prop)
    (hev : ∀ vs m', evalInst fr m st.inst = .ok (vs, m') → evalInst fr' m st'.inst = .ok (g vs, m'))
    (htr : ∀ c, evalInst fr m st.inst = .trap c → evalInst fr' m st'.inst = .trap c)
    (hset : ∀ vs regs, fr.regs.setMany st.results vs = some regs →
      ∃ regs', fr'.regs.setMany st'.results (g vs) = some regs' ∧
        P { fr with regs, body := rest } { fr' with regs := regs', body := rest' }) :
    (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧ P X1 Y1) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep fr m = r →
      lstep fr' m = r) := by
  rw [lstep_inst hb hc, lstep_inst hb' hc']
  refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
  · cases he : evalInst fr m st.inst with
    | ok p =>
      obtain ⟨vs, m'⟩ := p
      rw [he] at h; simp only [LRes.ofRes] at h
      rw [hev vs m' he]; simp only [LRes.ofRes]
      cases hs : fr.regs.setMany st.results vs with
      | none => simp only [hs] at h; cases h
      | some regs =>
        simp only [hs, LRes.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨regs', hs', hP⟩ := hset vs regs hs
        simp only [hs']
        exact ⟨_, rfl, hP⟩
    | trap c => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h
  · cases he : evalInst fr m st.inst with
    | ok p =>
      obtain ⟨vs, m'⟩ := p
      rw [he] at h; simp only [LRes.ofRes] at h
      split at h
      · exact absurd h.symm (hn _ _)
      · exact absurd h.symm (hs _)
    | trap c => rw [he] at h; rw [htr c he]; exact h
    | stuck msg => rw [he] at h; exact absurd h.symm (hs _)

/-- **One local step** of a frame of `f` is matched by one of the related frame of
`retype σ f`. -/
theorem rr_step {f : Function} (hok : okB σ f = true) {fr fr' : Frame} (m : Mem)
    (hr : RR σ f fr fr') :
    (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧ RR σ f X1 Y1) ∧
    (∀ ext vals rs rest, lstep fr m = .call ext vals rs rest →
      lstep fr' m = .call ext vals rs (rest.map (retypeStmt σ))) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ ext vals rs rest, r ≠ .call ext vals rs rest) →
      (∀ msg, r ≠ .stuck msg) → lstep fr m = r → lstep fr' m = r) := by
  obtain ⟨hf, hg, hsl, hbd, htm, ⟨b, hb, hsuf, htb⟩, hrr⟩ := hr
  obtain ⟨-, hsts, hterm⟩ := okB_block hok hb
  have hgl : fr'.func.globals = fr.func.globals := by rw [hf, hg]; rfl
  have hex : fr'.func.externs = fr.func.externs := by rw [hf, hg]; rfl
  have hext : ∀ fn, fr'.func.extern? fn = fr.func.extern? fn := by
    intro fn; simp only [Function.extern?, hex]
  cases hbody : fr.body with
  | cons st rest =>
    have hst : st ∈ b.body := hsuf.subset (by rw [hbody]; simp)
    have hok1 := hsts st hst
    have hbd' : fr'.body = retypeStmt σ st :: rest.map (retypeStmt σ) := by rw [hbd, hbody]; rfl
    have hpos : ∃ b ∈ f.blocks, rest <:+ b.body ∧ fr.term = b.term :=
      ⟨b, hb, (List.suffix_cons st rest).trans (hbody ▸ hsuf), htb⟩
    by_cases hc : ∃ fn args, st.inst = .call fn args
    · obtain ⟨fn, args, hi⟩ := hc
      have hi' : (retypeStmt σ st).inst = .call fn args := retypeInst_call.2 hi
      have hca : callArgs fr' fn args = callArgs fr fn args := by
        have hops := (stmtOk_other hok1 (by rw [hi]; rfl) (by rw [hi]; rfl)).1
        simp only [hi, operands] at hops
        unfold callArgs
        rw [hrr.getMany hops, hext fn]
      rw [lstep_call hbody hi, lstep_call hbd' hi', hca]
      refine ⟨fun X1 m1 h => ?_, fun ext vals rs rest' h => ?_, fun r hn hcl hs h => ?_⟩
      · cases hc : callArgs fr fn args <;> rw [hc] at h <;> cases h
      · cases hc : callArgs fr fn args with
        | ok p =>
          obtain ⟨e, vs⟩ := p
          rw [hc] at h
          simp only [LRes.ofRes, LRes.call.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, rfl, rfl⟩
        | trap c => rw [hc] at h; simp [LRes.ofRes] at h
        | stuck msg => rw [hc] at h; simp [LRes.ofRes] at h
      · cases hc : callArgs fr fn args with
        | ok p => rw [hc] at h; exact absurd h.symm (hcl _ _ _ _)
        | trap c => rw [hc] at h; exact h
        | stuck msg => rw [hc] at h; exact absurd h.symm (hs _)
    · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
      have hnc' : ∀ fn args, (retypeStmt σ st).inst ≠ .call fn args :=
        fun fn args h => hnc fn args (retypeInst_call.1 h)
      have hncall : ∀ ext vals rs rest', lstep fr m ≠ .call ext vals rs rest' := by
        intro ext vals rs rest' h
        obtain ⟨st0, fn, args, hb0, hi0, -⟩ := lstep_call_inv h
        rw [hbody] at hb0; cases hb0
        exact hnc fn args hi0
      suffices H : (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧
          RR σ f X1 Y1) ∧ (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) →
          lstep fr m = r → lstep fr' m = r) from
        ⟨H.1, fun ext vals rs rest' h => absurd h (hncall _ _ _ _),
          fun r hn _ hs h => H.2 r hn hs h⟩
      have mkRR : ∀ regs regs', RegRel σ (vals σ f) regs regs' →
          RR σ f { fr with regs, body := rest } { fr' with regs := regs', body := rest.map (retypeStmt σ) } :=
        fun regs regs' h => ⟨hf, hg, hsl, rfl, htm, hpos, h⟩
      cases hl : isRLoad σ st.inst
      · cases hs : isRStore σ st.inst
        · -- any other statement: the same instruction on equal operands
          obtain ⟨hops, hres⟩ := stmtOk_other hok1 hl hs
          have hi' : (retypeStmt σ st).inst = st.inst := retypeInst_other hl hs
          have hev : evalInst fr' m (retypeStmt σ st).inst = evalInst fr m st.inst := by
            rw [hi']; exact evalInst_congr hgl hex hsl fun x hx => hrr.1 x (hops x hx)
          refine lstep_inst_rel hbody hbd' hnc hnc' id _ (fun vs m' h => by rw [hev, h]; rfl)
            (fun c h => by rw [hev, h]) fun vs regs h => ?_
          obtain ⟨regs', h', hrr'⟩ := hrr.setMany hres h
          exact ⟨regs', h', mkRR _ _ hrr'⟩
        · -- a retyped store: the stored value retagged, the same bytes
          obtain ⟨t, fl, x, p, off, hi, hx, hp, hres⟩ := stmtOk_rstore hok1 hl hs
          obtain ⟨t0, t', fl0, x0, p0, off0, hi0, ht, hri⟩ := isRStore_spec hs
          rw [hi] at hi0; cases hi0
          have hri' : (retypeStmt σ st).inst = .store .store t' fl x p off := hri
          obtain ⟨hev, htr⟩ := evalInst_rstore (m := m) (fr := fr) (fr' := fr') ht (hrr.1 p hp)
            (hrr.2 x hx)
          refine lstep_inst_rel hbody hbd' hnc hnc' id _ (fun vs m' h => by
            rw [hri']; rw [hi] at h; exact hev vs m' h) (fun c h => by
            rw [hri']; rw [hi] at h; exact htr c h) fun vs regs h => ?_
          obtain ⟨regs', h', hrr'⟩ := hrr.setMany (xs := st.results)
            (by rw [hres]; intro x hx; cases hx) h
          exact ⟨regs', h', mkRR _ _ hrr'⟩
      · -- a retyped load: the loaded value retagged
        obtain ⟨hlen, hops⟩ := stmtOk_rload hok1 hl
        obtain ⟨t, t', fl, p, off, hi, ht, hri⟩ := isRLoad_spec hl
        have hp : p ∉ vals σ f := hops p (by rw [hi]; simp [operands])
        obtain ⟨hev, htr⟩ := evalInst_rload (m := m) (fr := fr) (fr' := fr') (fl := fl) (off := off)
          ht (hrr.1 p hp)
        obtain ⟨r, hr1⟩ := List.length_eq_one_iff.1 hlen
        have hrV : r ∈ vals σ f := mem_vals hb hst hl r (by rw [hr1]; simp)
        have hri' : (retypeStmt σ st).inst = .load .load t' fl p off := hri
        refine lstep_inst_rel hbody hbd' hnc hnc' (List.map (retag σ)) _ (fun vs m' h => by
          rw [hri']; rw [hi] at h; exact hev vs m' h) (fun c h => by
          rw [hri']; rw [hi] at h; exact htr c h) fun vs regs h => ?_
        have h1 : fr.regs.setMany [r] vs = some regs := by rw [← hr1]; exact h
        obtain ⟨regs', h', hrr'⟩ := hrr.set1 hrV h1
        exact ⟨regs', by show fr'.regs.setMany st.results _ = _; rw [hr1]; exact h', mkRR _ _ hrr'⟩
  | nil =>
    have hncall : ∀ ext vals rs rest', lstep fr m ≠ .call ext vals rs rest' := by
      intro ext vals rs rest' h
      obtain ⟨st0, -, -, hb0, -⟩ := lstep_call_inv h
      rw [hbody] at hb0; cases hb0
    suffices H : (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧
        RR σ f X1 Y1) ∧ (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) →
        lstep fr m = r → lstep fr' m = r) from
      ⟨H.1, fun ext vals rs rest' h => absurd h (hncall _ _ _ _), fun r hn _ hs h => H.2 r hn hs h⟩
    have hbd' : fr'.body = [] := by rw [hbd, hbody]; rfl
    have hops : ∀ v ∈ termOperands fr.term, v ∉ vals σ f := by rw [htb]; exact hterm
    have henter : ∀ bc : BlockCall, (∀ v ∈ bc.args, v ∉ vals σ f) → ∀ X1 m1,
        LRes.ofRes (enterBlock fr bc) (fun fr1 => .next fr1 m) = .next X1 m1 →
        ∃ Y1, LRes.ofRes (enterBlock fr' bc) (fun fr1 => .next fr1 m) = .next Y1 m1 ∧
          RR σ f X1 Y1 := by
      intro bc hbc X1 m1 h
      cases he : enterBlock fr bc with
      | ok X2 =>
        rw [he] at h; simp only [LRes.ofRes, LRes.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨Y1, he', hR⟩ := enterBlock_rr hok hf hg hsl hrr hbc he
        exact ⟨Y1, by rw [he']; rfl, hR⟩
      | trap c => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
    have hnr : ∀ (bc : BlockCall) r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) →
        LRes.ofRes (enterBlock fr bc) (fun fr1 => LRes.next fr1 m) ≠ r := by
      intro bc r hn hs h
      cases he : enterBlock fr bc with
      | ok X1 => rw [he] at h; exact hn X1 m h.symm
      | trap c => exact enterBlock_not_trap _ _ _ he
      | stuck msg => rw [he] at h; exact hs msg h.symm
    rw [lstep_term hbody, lstep_term hbd', htm]
    cases hterm' : fr.term with
    | jump d =>
      have hops' : ∀ v ∈ termOperands (.jump d), v ∉ vals σ f := hterm' ▸ hops
      exact ⟨fun X1 m1 h => henter d hops' X1 m1 h, fun r hn hs h => absurd h (hnr d r hn hs)⟩
    | brif c t e =>
      have hops' : ∀ v ∈ termOperands (.brif c t e), v ∉ vals σ f := hterm' ▸ hops
      have hgc : fr'.get c = fr.get c := hrr.frameGet (hops' c (by simp [termOperands]))
      simp only [hgc]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : fr.get c with
        | ok cv =>
          simp only [hcv, LRes.ofRes] at h ⊢
          refine henter _ (fun v hv => hops' v ?_) X1 m1 h
          simp only [termOperands, List.mem_cons, List.mem_append]
          split at hv <;> simp [hv]
        | trap _ => simp [hcv, LRes.ofRes] at h
        | stuck _ => simp [hcv, LRes.ofRes] at h
      · cases hcv : fr.get c with
        | ok cv => simp only [hcv, LRes.ofRes] at h; exact absurd h (hnr _ r hn hs)
        | trap _ => simp only [hcv, LRes.ofRes] at h ⊢; exact h
        | stuck msg => simp only [hcv, LRes.ofRes] at h; exact absurd h.symm (hs _)
    | brTable x d tbl =>
      have hops' : ∀ v ∈ termOperands (.brTable x d tbl), v ∉ vals σ f := hterm' ▸ hops
      have hgx : fr'.get x = fr.get x := hrr.frameGet (hops' x (by simp [termOperands]))
      simp only [hgx]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : fr.get x with
        | ok xv =>
          simp only [hcv, LRes.ofRes] at h ⊢
          refine henter _ (fun v hv => hops' v ?_) X1 m1 h
          simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
          cases hq : tbl[xv.toNat]? with
          | none => rw [hq] at hv; exact .inl (.inr hv)
          | some q => rw [hq] at hv; exact .inr ⟨q, List.mem_of_getElem? hq, hv⟩
        | trap _ => simp [hcv, LRes.ofRes] at h
        | stuck _ => simp [hcv, LRes.ofRes] at h
      · cases hcv : fr.get x with
        | ok xv => simp only [hcv, LRes.ofRes] at h; exact absurd h (hnr _ r hn hs)
        | trap _ => simp only [hcv, LRes.ofRes] at h ⊢; exact h
        | stuck msg => simp only [hcv, LRes.ofRes] at h; exact absurd h.symm (hs _)
    | ret xs =>
      have hops' : ∀ v ∈ xs, v ∉ vals σ f := by rw [hterm'] at hops; exact hops
      simp only [hrr.getMany hops']
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : fr.getMany xs <;> simp [hg, LRes.ofRes] at h
    | returnCall fn args =>
      have hops' : ∀ v ∈ args, v ∉ vals σ f := by rw [hterm'] at hops; exact hops
      have hta : tailArgs fr' fn args = tailArgs fr fn args := by
        have hsig : fr'.func.sig = fr.func.sig := by rw [hf, hg]; rfl
        unfold tailArgs
        rw [hrr.getMany hops', hext fn, hsig]
      simp only [hta]
      refine ⟨fun X1 m1 h => ?_, fun r _ _ h => h⟩
      cases hg : tailArgs fr fn args <;> simp [hg, LRes.ofRes] at h
    | trap c => exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
    | tryCall fn args et => exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩
    | tryCallIndirect c args et => exact ⟨fun X1 m1 h => (by cases h), fun r _ _ h => h⟩

end Opt.Retype

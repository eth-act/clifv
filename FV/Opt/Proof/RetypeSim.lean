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

end Opt.Retype

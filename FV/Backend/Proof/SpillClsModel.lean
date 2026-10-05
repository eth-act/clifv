import FV.Backend.Proof.SpillClsTab
import FV.Backend.Proof.SpillClsExt
import FV.Backend.Proof.IselCovDriver

/-!
# The class model of the driver's ISLE calls (V4 classes)

`clsModel`: an abstract value of flow level `≤ 1` describes values whose registers have the
classes the lowering state records (`GoodV`); the state invariant `ClsIs s0` says the classes
cover the allocated vregs, the values' and `try_call` registers have their classes, and every
instruction emitted since `s0` holds registers of their classes. With `clsTab` (`clsTab_ok`
and the root checks of `SpillClsTab`):

* `stmt_cls`: a statement's `lower` keeps `ClsIs`, and its result (with results) is `GoodV`;
* `termCall_cls`, `tryCall_cls`: so do a terminator's and a `try_call`'s lowering.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Every register of `v` has the class `cls` records. -/
def GoodV (cls : Array RegClass) (v : V) : Prop := ∀ r ∈ v.regsIn, RegCls cls r

/-- The class meaning of an abstract value: at flow level `≤ 1`, `GoodV`. -/
def γC (a : FA) (st : LState) (v : V) : Prop := a.f ≤ 1 → GoodV st.classes v

/-- The state invariant of a run from `s0`. -/
structure ClsIs (ctx : Ctx) (s0 st : LState) : Prop where
  sz : Sz st
  vals : ∀ x r, ctx.valueReg? x = some r → RegCls st.classes r
  try1 : ∀ r ∈ ctx.tryRegs.1, RegCls st.classes r
  try2 : ∀ r ∈ ctx.tryRegs.2, RegCls st.classes r
  emitted : ∃ ms : List MInst, st.emitted = s0.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, RegsFrom (RegCls st.classes) m

section Model
variable {ctx : Ctx} (hcl : Cov.Clean ctx)

include hcl in
theorem γC_ext (st : LState) (a : FA) (term : Term) (v : V) (fs : List V)
    (_hv : γC a st v) (h : (sem ctx).extract term v st = .ok fs) :
    ∀ w ∈ fs, γC (aext term.id a) st w := by
  have hs := externExtract_ok ctx term v st fs h
  intro w hw hf
  unfold aext at hf
  split at hf
  · rename_i hcond
    have := (hs.c0 (by simpa [Bool.or_eq_true, List.contains_iff_mem] using hcond) w hw).1
    intro r hr; rw [this] at hr; cases hr
  · split at hf
    · rename_i _ hcond
      have := (hs.val (by simpa [List.contains_iff_mem] using hcond) w hw).1
      intro r hr; rw [this] at hr; cases hr
    · split at hf
      · rename_i _ _ hid
        obtain ⟨i, info', rfl, hinfo, rfl⟩ := hs.idv (by simpa using hid)
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · intro r hr; simp [V.regsIn] at hr
        · intro r hr; rw [(hcl _ _ hinfo).1] at hr; cases hr
      · split at hf
        · rename_i _ _ _ hid
          obtain ⟨i, info', r, rfl, hinfo, hr, rfl⟩ := hs.fr (by simpa using hid)
          simp only [List.mem_singleton] at hw
          subst hw
          intro r hr; simp [V.regsIn] at hr
        · simp [FA.top] at hf

theorem apreC_args {id : TermId} {as : List FA} (hpre : apreC false id as = true) (hid : id ∈ emitIds) :
    ∀ a ∈ as, a.f ≤ 1 := by
  have : (id != TId.emit && id != TId.gen_return && id != TId.gen_call_args) = false := by
    simp only [emitIds, List.mem_cons, List.mem_nil_iff, or_false] at hid
    rcases hid with h | h | h <;> simp [h]
  rw [apreC, this, Bool.false_or] at hpre
  exact fun a ha => by simpa using List.all_eq_true.mp hpre a ha

theorem γC_ctor (s0 st : LState) (as : List FA) (vs : List V) (term : Term) (v : V) (st' : LState)
    (hvs : Holds2 γC st as vs) (hIs : ClsIs ctx s0 st) (hpre : apreC false term.id as = true)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γC (actor term.id as) st' v ∧ ClsIs ctx s0 st' := by
  have hc := externCtor_cls ctx term vs st v st' h
  have hargs : (∀ a ∈ as, a.f ≤ 1) → ∀ r ∈ regsInL vs, RegCls st'.classes r := fun hall r hr => by
    obtain ⟨w, hw, hrw⟩ := regsInL_mem hr
    obtain ⟨a, ha, hwa⟩ := holds2_mem hvs w hw
    exact regCls_step hc.step (hwa (hall a ha) r hrw)
  refine ⟨fun hf => ?_, ?_⟩
  · unfold actor at hf
    split at hf
    · simp at hf
    · rename_i hid
      have hall : ∀ a ∈ as, a.f ≤ 1 := fun a ha => joinAll_f hf a ha
      intro r hr
      rcases hc.regs hIs.sz r hr with h1 | h1 | ⟨x, -, hx⟩ | h1 | h1 | h1
      · exact hargs hall r h1
      · exact h1
      · exact regCls_step hc.step (hIs.vals x r hx)
      · exact absurd (beq_iff_eq.mpr h1) hid
      · exact regCls_step hc.step (hIs.try1 r h1)
      · exact regCls_step hc.step (hIs.try2 r h1)
  · obtain ⟨ms0, h0, h1⟩ := hIs.emitted
    obtain ⟨ms, h2, h3⟩ := hc.emit
    refine ⟨sz_step hc.step hIs.sz, fun x r hx => regCls_step hc.step (hIs.vals x r hx),
      fun r hr => regCls_step hc.step (hIs.try1 r hr), fun r hr => regCls_step hc.step (hIs.try2 r hr),
      ms0 ++ ms, by rw [h2, h0]; simp, fun m hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact (h1 m hm).mono fun r hr => regCls_step hc.step hr
    · refine (h3 hIs.sz m hm).mono fun r hr => ?_
      rcases hr with ⟨hid, hr⟩ | hr
      · exact hargs (apreC_args hpre hid) r hr
      · exact hr

/-- **The class model** of the driver's semantics, from `s0`. -/
def clsModel (s0 : LState) : ModelC (sem ctx) false where
  γ := γC
  Is := ClsIs ctx s0
  Rs := ClsStep
  rs_refl := clsStep_refl
  rs_trans := fun _ _ _ => clsStep_trans
  rs_ctor := fun term vs s v s' h => (externCtor_cls ctx term vs s v s' h).step
  top := fun _ _ h => by simp [FA.top] at h
  le := fun a b _ _ hab ha hb => by
    simp only [FA.le, Bool.and_eq_true, decide_eq_true_eq] at hab
    exact ha (Nat.le_trans hab.1 hb)
  mono := fun _ _ _ _ h hv hf r hr => regCls_step h (hv hf r hr)
  int := fun _ _ _ _ r hr => by simp [sem, V.regsIn] at hr
  bool := fun _ _ _ r hr => by simp [sem, V.regsIn] at hr
  prim := fun _ _ _ _ h _ r hr => by
    obtain ⟨t, rfl⟩ := sem_prim_eq ctx h
    simp [V.regsIn] at hr
  mkd := fun st ty k as vs h hf r hr => by
    rw [amk_f] at hf
    have hr' : r ∈ regsInL vs := by simpa [sem, V.regsIn] using hr
    obtain ⟨w, hw, hrw⟩ := regsInL_mem hr'
    obtain ⟨a, ha, hwa⟩ := holds2_mem h w hw
    exact hwa (joinAll_f hf a ha) r hrw
  un := fun st a ty v k fs hv hu => by
    have := sem_unData_eq ctx hu
    subst this
    intro w hw hf r hr
    exact hv hf r (by simpa [V.regsIn] using regsIn_sub_of_mem hw r hr)
  ext := γC_ext hcl
  ctor := fun st as vs term v st' hvs hIs hpre h => γC_ctor s0 st as vs term v st' hvs hIs hpre h

end Model

end Backend.Proof.Spill

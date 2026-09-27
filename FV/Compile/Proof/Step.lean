import FV.Compile.Proof.Sim

/-!
# Calls: fresh result ids, extern declarations, extern-call steps
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame State Mem Program Function Block Inst Terminator Outcome
  StepResult Signature ExtFunc FnRef)

theorem freshFor_run : ∀ (tys : List Clif.Ty) (cg : CG),
    (freshFor tys).run cg = (List.range' cg.nextVal tys.length,
      { cg with nextVal := cg.nextVal + tys.length })
  | [], cg => rfl
  | t :: tys, cg => by
    have := freshFor_run tys { cg with nextVal := cg.nextVal + 1 }
    simp only [freshFor] at this ⊢
    rw [List.mapM_cons]
    simp only [bind_run, fresh_run, pure_run]
    rw [this]
    simp [List.range'_succ, Nat.add_assoc, Nat.add_comm 1]

/-- Extern-declaration keys are indices. -/
def ExtIdx (F : Function) : Prop := ∀ i (h : i < F.externs.length), F.externs[i].1 = i

theorem lookup_idx {α : Type} : ∀ (l : List (Nat × α)) (o : Nat),
    (∀ i (h : i < l.length), l[i].1 = i + o) → ∀ i (hi : i < l.length),
    l.lookup (i + o) = some l[i].2
  | [], _, _, i, hi => by simp at hi
  | (k, v) :: l, o, h, i, hi => by
    have h0 := h 0 (by simp)
    simp at h0; subst h0
    cases i with
    | zero => simp [List.lookup]
    | succ i =>
      simp only [List.lookup]
      rw [show (i + 1 + k == k) = false by simp]
      have := lookup_idx l (k + 1) (fun j hj => by
        have := h (j + 1) (by simp; omega); simp at this; omega) i (by simp at hi; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem lookup_of_idx {α : Type} {l : List (Nat × α)} (hidx : ∀ i (h : i < l.length), l[i].1 = i)
    {r : Nat} {a : α} (hm : (r, a) ∈ l) : l.lookup r = some a := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have hr : r = i := by rw [← hidx i hi, he]
  subst hr
  have := lookup_idx l 0 (by simpa using hidx) r hi
  rw [he] at this; simpa using this

theorem declare_lookup {F : Function} (hx : ExtIdx F) {name : String} {sig : Signature}
    {cg : CG} (hL : Lk F ((declare name sig).run cg).2) :
    ∃ e, F.externs.lookup ((declare name sig).run cg).1 = some e ∧ e.name = name ∧ e.sig = sig := by
  obtain ⟨-, hpre, -⟩ := hL
  have hmem : ∃ e, (((declare name sig).run cg).1, e) ∈ ((declare name sig).run cg).2.externs ∧
      e.name = name ∧ e.sig = sig := by
    rw [declare_run]
    split
    · rename_i r e' hf
      have := List.find?_some hf
      simp at this
      exact ⟨e', List.mem_of_find?_eq_some hf, this.1, this.2⟩
    · exact ⟨{ name, sig }, by simp, rfl, rfl⟩
  obtain ⟨e, hm, hn, hs⟩ := hmem
  exact ⟨e, lookup_of_idx hx (hpre.subset hm), hn, hs⟩

/-- Names of the map runtime externs. -/
def rtNames : List String :=
  ["flat_map_new", "flat_map_insert", "flat_map_contains", "flat_map_get", "flat_map_clone",
    "flat_map_len", "flat_map_entry"]

/-- The program has no function with a runtime extern's name. -/
def RtOK (P : Program) : Prop := ∀ n ∈ rtNames, P.func? n = none

theorem callFn_run (name : String) (sig : Signature) (args : List ValueId) (cg : CG) :
    (callFn name sig args).run cg =
      (List.range' cg.nextVal sig.returns.length,
       { ((declare name sig).run cg).2 with
         nextVal := cg.nextVal + sig.returns.length,
         curBody := ⟨List.range' cg.nextVal sig.returns.length, .call ((declare name sig).run cg).1 args⟩ ::
           cg.curBody }) := by
  simp only [callFn, bind_run, emitStmt_run, pure_run, freshFor_run, List.length_map]
  have h := Bk.declare_eq name sig cg
  obtain ⟨-, -, -, hb, -, -⟩ := h
  have hnv : ((declare name sig).run cg).2.nextVal = cg.nextVal := by
    rw [declare_run]; split <;> rfl
  rw [hnv, hb]

section
variable {E : Clif.Env} {P : Program}

/-- A call of an `Env` extern that returns. -/
theorem reach_callExt {F : Function} (hx : ExtIdx F) {cg : CG} {s : State} {name : String}
    {sig : Signature} {args : List ValueId} {vals rvals : List Val} {m' : Mem}
    {f : List Val → Mem → Outcome} {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good F ((callFn name sig args).run cg).2) (hAt : At F cg s.frame)
    (hargs : RegsHas s.frame.regs args vals) (htys : vals.map (·.ty) = sig.params.map (·.ty))
    (hP : P.func? name = none) (hext : E.extern name = some f)
    (hres : f vals s.mem = .returned rvals m') (hrt : rvals.map (·.ty) = sig.returns.map (·.ty))
    (k : ∀ fr' : Frame, At F ((callFn name sig args).run cg).2 fr' →
      RegsHas fr'.regs ((callFn name sig args).run cg).1 rvals →
      Agree s.frame.regs fr'.regs cg.nextVal → fr'.func = s.frame.func →
      fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr', mem := m' }) :
    Reach E P Q X s := by
  have hLd : Lk F ((declare name sig).run cg).2 := by
    have h := hG.1; rw [callFn_run] at h; exact h
  obtain ⟨e, hlk, hn, hs⟩ := declare_lookup hx hLd
  obtain ⟨rest, hb, hA'⟩ := At.emit (cg := cg) (cg' := ((callFn name sig args).run cg).2)
    (st := ⟨List.range' cg.nextVal sig.returns.length, .call ((declare name sig).run cg).1 args⟩)
    (by rw [callFn_run]; rw [(Bk.declare_eq name sig cg).2.1])
    (by rw [callFn_run]) hG hAt
  have hlen : (List.range' cg.nextVal sig.returns.length).length = rvals.length := by
    have := congrArg List.length hrt; simp at this ⊢; omega
  obtain ⟨regs', hr⟩ := setMany_some s.frame.regs _ _ hlen
  have hstep : Clif.step E P s =
      StepResult.next { s with frame := { s.frame with regs := regs', body := rest }, mem := m' } := by
    rw [Clif.step_call E P s rest _ _ _ hb]
    simp only [Clif.stepCall, getMany_of_regsHas s.frame hargs]
    have hlk' : s.frame.func.extern? ((declare name sig).run cg).1 = some e := by
      rw [hAt.1]; exact hlk
    simp only [hlk', Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.checkTys,
      Clif.AbiParam.tys, hs, htys, beq_self_eq_true, Clif.Res.check_true, StepResult.ofRes_ok,
      Clif.Res.pure_eq, hn, hP, hext, hres, hrt, ↓reduceIte, Clif.continueWith]
    rw [hr]
  refine .next hstep (k _ (hA'.congr rfl rfl rfl) ?_ ?_ rfl rfl)
  · rw [show ((callFn name sig args).run cg).1 = List.range' cg.nextVal sig.returns.length by
      rw [callFn_run]]
    exact setMany_has List.nodup_range' hr
  · exact setMany_agree hr fun x hx => (List.mem_range'_1.1 hx).1

/-- A call of an `Env` extern that traps. -/
theorem reach_callExt_trap {F : Function} (hx : ExtIdx F) {cg : CG} {s : State} {name : String}
    {sig : Signature} {args : List ValueId} {vals : List Val} {c : Clif.TrapCode}
    {f : List Val → Mem → Outcome} {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good F ((callFn name sig args).run cg).2) (hAt : At F cg s.frame)
    (hargs : RegsHas s.frame.regs args vals) (htys : vals.map (·.ty) = sig.params.map (·.ty))
    (hP : P.func? name = none) (hext : E.extern name = some f)
    (hres : f vals s.mem = .trapped c) (hX : X (.trapped c)) :
    Reach E P Q X s := by
  have hLd : Lk F ((declare name sig).run cg).2 := by
    have h := hG.1; rw [callFn_run] at h; exact h
  obtain ⟨e, hlk, hn, hs⟩ := declare_lookup hx hLd
  obtain ⟨rest, hb, -⟩ := At.emit (cg := cg) (cg' := ((callFn name sig args).run cg).2)
    (st := ⟨List.range' cg.nextVal sig.returns.length, .call ((declare name sig).run cg).1 args⟩)
    (by rw [callFn_run]; rw [(Bk.declare_eq name sig cg).2.1])
    (by rw [callFn_run]) hG hAt
  refine .trap (c := c) ?_ hX
  rw [Clif.step_call E P s rest _ _ _ hb]
  simp only [Clif.stepCall, getMany_of_regsHas s.frame hargs]
  have hlk' : s.frame.func.extern? ((declare name sig).run cg).1 = some e := by
    rw [hAt.1]; exact hlk
  simp only [hlk', Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.checkTys,
    Clif.AbiParam.tys, hs, htys, beq_self_eq_true, Clif.Res.check_true, StepResult.ofRes_ok,
    Clif.Res.pure_eq, hn, hP, hext, hres]

end

end Compile.Proof

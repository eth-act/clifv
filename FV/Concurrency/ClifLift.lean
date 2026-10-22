import FV.Concurrency.ClifCStepTerm

/-!
# Lifting CLIF thread runs below suspended callers (T2h, #311, layer 4b)

A callee's run from its own entry state (`callers = []`) is a run of the caller's thread, whose
state has the caller's suspended frames below the callee's (`pushC ext s`):

* `step_pushC`: `Clif.step` reads the callers only to push onto them or to return to the
  topmost one, so a step of `pushC ext s` is the step of `s` with the callers pushed (`push`): a
  return of the bottom frame (`done`) resumes the first of `ext`;
* `cstep_pushC`: the same for the CLIF thread steps (`CStep`) between running states;
* `crun_pushC`: a CLIF run, lifted: all its steps but a last return of the bottom frame, which
  has no events.
-/

namespace Concurrency.ClifLift

open Prog ClifThread ClifCStepTerm

/-- `s` with the suspended callers `ext` below its own. -/
def pushC (ext : List (Clif.Frame × List Clif.ValueId)) (s : Clif.State) : Clif.State :=
  { s with callers := s.callers ++ ext }

/-- A step result of a state with the extra callers `ext`: a return from the bottom frame resumes
the first of `ext`. -/
def push (ext : List (Clif.Frame × List Clif.ValueId)) : Clif.StepResult → Clif.StepResult
  | .next s => .next (pushC ext s)
  | .done vals mem => match ext with
    | [] => .done vals mem
    | (caller, results) :: rest => match caller.regs.setMany results vals with
      | some regs => .next { frame := { caller with regs }, callers := rest, mem }
      | none => .stuck "call result arity mismatch"
  | r => r

theorem withBytes_pushC (ext : List (Clif.Frame × List Clif.ValueId)) (s : Clif.State)
    (B : Bytes) : withBytes (pushC ext s) B = pushC ext (withBytes s B) := rfl

theorem push_ofRes {α : Type} (ext : List (Clif.Frame × List Clif.ValueId)) (r : Clif.Res α)
    (k : α → Clif.StepResult) :
    push ext (Clif.StepResult.ofRes r k) = Clif.StepResult.ofRes r fun a => push ext (k a) := by
  cases r <;> rfl

theorem continueWith_pushC (ext : List (Clif.Frame × List Clif.ValueId)) (s : Clif.State) rest
    results vals mem :
    Clif.continueWith (pushC ext s) rest results vals mem =
      push ext (Clif.continueWith s rest results vals mem) := by
  unfold Clif.continueWith
  simp only [pushC]
  split <;> rfl

theorem returnValues_pushC (ext : List (Clif.Frame × List Clif.ValueId)) (s : Clif.State) vals
    mem : Clif.returnValues (pushC ext s) vals mem = push ext (Clif.returnValues s vals mem) := by
  unfold Clif.returnValues
  rw [push_ofRes]
  congr 1
  funext _
  simp only [pushC]
  rcases s.callers with _ | ⟨⟨caller, results⟩, cs⟩
  · rfl
  · simp only [List.cons_append]
    split <;> rfl

theorem stepCall_pushC (env : Clif.Env) (p : Clif.Program) ext (s : Clif.State) rest results fn
    args : Clif.stepCall env p (pushC ext s) rest results fn args =
      push ext (Clif.stepCall env p s rest results fn args) := by
  unfold Clif.stepCall
  dsimp only
  rw [push_ofRes]
  congr 1
  funext ⟨e, vals⟩
  simp only [pushC]
  cases p.func? e.name with
  | some callee =>
    dsimp only
    split
    · rw [push_ofRes]; rfl
    · rfl
  | none =>
    dsimp only
    cases env.extern e.name with
    | none => rfl
    | some f =>
      dsimp only
      cases f vals s.mem with
      | returned rvals mem' =>
        dsimp only
        split
        · exact continueWith_pushC ext s rest results _ _
        · rfl
      | _ => rfl

theorem stepCallIndirect_pushC (env : Clif.Env) (p : Clif.Program) ext (s : Clif.State) rest
    results sig callee args : Clif.stepCallIndirect env p (pushC ext s) rest results sig callee args =
      push ext (Clif.stepCallIndirect env p s rest results sig callee args) := by
  unfold Clif.stepCallIndirect
  dsimp only
  rw [push_ofRes]
  congr 1
  funext ⟨declared, addr, vals⟩
  simp only [pushC]
  cases List.find? (fun f => s.mem.symbols f.name == some addr) p.funcs with
  | some target =>
    dsimp only
    split
    · rw [push_ofRes]; rfl
    · rfl
  | none =>
    dsimp only
    rw [push_ofRes]
    congr 1
    funext ⟨rvals, mem'⟩
    exact continueWith_pushC ext s rest results _ _

theorem stepReturnCall_pushC (env : Clif.Env) (p : Clif.Program) ext (s : Clif.State) fn args :
    Clif.stepReturnCall env p (pushC ext s) fn args =
      push ext (Clif.stepReturnCall env p s fn args) := by
  unfold Clif.stepReturnCall
  dsimp only
  rw [push_ofRes]
  congr 1
  funext ⟨e, vals⟩
  simp only [pushC]
  cases p.func? e.name with
  | some callee =>
    dsimp only
    split
    · rw [push_ofRes]; rfl
    · rfl
  | none =>
    dsimp only
    cases env.extern e.name with
    | none => rfl
    | some f =>
      dsimp only
      cases f vals s.mem with
      | returned rvals mem' => exact returnValues_pushC ext s _ _
      | _ => rfl

theorem stepTerm_pushC (env : Clif.Env) (p : Clif.Program) ext (s : Clif.State) term :
    Clif.stepTerm env p (pushC ext s) term = push ext (Clif.stepTerm env p s term) := by
  cases term with
  | jump dest => simp only [Clif.stepTerm, push_ofRes]; rfl
  | brif c t e =>
    simp only [Clif.stepTerm, push_ofRes]
    rfl
  | brTable x dflt table =>
    simp only [Clif.stepTerm, push_ofRes]
    rfl
  | ret xs =>
    simp only [Clif.stepTerm, push_ofRes]
    congr 1
    funext vals
    exact returnValues_pushC ext s _ _
  | returnCall fn args => exact stepReturnCall_pushC env p ext s fn args
  | trap code => rfl
  | tryCall fn args et =>
    simp only [Clif.stepTerm, Clif.stepTryCall, push_ofRes]
    congr 1
    funext ⟨n, base, bc⟩
    exact stepCall_pushC env p ext
      { s with frame := { s.frame with body := [], term := .jump bc } } [] _ fn args
  | tryCallIndirect callee args et =>
    simp only [Clif.stepTerm, Clif.stepTryCallIndirect, push_ofRes]
    congr 1
    funext ⟨n, base, bc⟩
    exact stepCallIndirect_pushC env p ext
      { s with frame := { s.frame with body := [], term := .jump bc } } [] _ _ callee args

/-- **A step below extra callers** is the step with the callers pushed. -/
theorem step_pushC (env : Clif.Env) (p : Clif.Program) (ext) (s : Clif.State) :
    Clif.step env p (pushC ext s) = push ext (Clif.step env p s) := by
  unfold Clif.step
  have hb : (pushC ext s).frame.body = s.frame.body := rfl
  rw [hb]
  cases s.frame.body with
  | nil => exact stepTerm_pushC env p ext s _
  | cons st rest =>
    dsimp only
    cases st.inst with
    | call fn args => exact stepCall_pushC env p ext s _ _ _ _
    | callIndirect sig callee args => exact stepCallIndirect_pushC env p ext s _ _ _ _ _
    | _ =>
      dsimp only
      rw [push_ofRes]
      congr 1
      funext ⟨vals, mem⟩
      exact continueWith_pushC ext s _ _ _ _

/-! ## Only a terminator finishes the run -/

theorem ofRes_ne_done {α : Type} (r : Clif.Res α) (k : α → Clif.StepResult)
    (h : ∀ a v m, k a ≠ .done v m) : ∀ v m, Clif.StepResult.ofRes r k ≠ .done v m := by
  intro v m
  cases r with
  | ok a => exact h a v m
  | trap c => nofun
  | stuck m' => nofun

theorem continueWith_ne_done (s : Clif.State) rest results vals mem :
    ∀ v m, Clif.continueWith s rest results vals mem ≠ .done v m := by
  intro v m
  unfold Clif.continueWith
  split <;> nofun

theorem stepCall_ne_done (env : Clif.Env) (p : Clif.Program) (s : Clif.State) rest results fn
    args : ∀ v m, Clif.stepCall env p s rest results fn args ≠ .done v m := by
  unfold Clif.stepCall
  dsimp only
  apply ofRes_ne_done
  rintro ⟨e, vals⟩ v m
  dsimp only
  split
  · split
    · exact ofRes_ne_done _ _ (fun a _ _ => by obtain ⟨_, _⟩ := a; nofun) v m
    · nofun
  · split
    · split
      · split
        · exact continueWith_ne_done _ _ _ _ _ v m
        · nofun
      all_goals nofun
    · nofun

theorem stepCallIndirect_ne_done (env : Clif.Env) (p : Clif.Program) (s : Clif.State) rest
    results sig callee args :
    ∀ v m, Clif.stepCallIndirect env p s rest results sig callee args ≠ .done v m := by
  unfold Clif.stepCallIndirect
  dsimp only
  apply ofRes_ne_done
  rintro ⟨declared, addr, vals⟩ v m
  dsimp only
  split
  · split
    · exact ofRes_ne_done _ _ (fun a _ _ => by obtain ⟨_, _⟩ := a; nofun) v m
    · nofun
  · exact ofRes_ne_done _ _ (fun a v m => by obtain ⟨_, _⟩ := a; exact continueWith_ne_done _ _ _ _ _ v m) v m

/-- A step that finishes the run is a terminator's. -/
theorem step_done_body {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {v m}
    (h : Clif.step env p s = .done v m) : s.frame.body = [] := by
  unfold Clif.step at h
  split at h
  · assumption
  · exfalso
    split at h
    · exact stepCall_ne_done env p s _ _ _ _ v m h
    · exact stepCallIndirect_ne_done env p s _ _ _ _ _ v m h
    · exact ofRes_ne_done _ _ (fun a v m => by obtain ⟨_, _⟩ := a; exact continueWith_ne_done _ _ _ _ _ v m) v m h

/-- A CLIF thread step that returns from the bottom frame has no events. -/
theorem cstep_ret_nil {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {evs} {v}
    (h : CStep env p (.run s) evs (.ret v)) : evs = [] := by
  have h0 := h
  obtain ⟨-, ⟨B, hB⟩, hf⟩ := h0
  obtain ⟨t'', hr, hst⟩ := hf B hB
  have hb : s.frame.body = [] := by
    cases hs : Clif.step env p (withBytes s B) with
    | done vals mem => exact step_done_body (s := withBytes s B) hs
    | next s2 =>
      rw [hs] at hr
      simp only [res, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      cases hst
    | trapped c => rw [hs] at hr; simp [res] at hr
    | stuck m => rw [hs] at hr; simp [res] at hr
  exact cstep_nil_of_shape (by unfold evShape; rw [hb]) h

/-! ## Steps and runs below extra callers -/

/-- **A CLIF thread step between running states, below extra callers.** -/
theorem cstep_pushC {env p ext} {s s' : Clif.State} {evs}
    (h : CStep env p (.run s) evs (.run s')) :
    CStep env p (.run (pushC ext s)) evs (.run (pushC ext s')) := by
  obtain ⟨hk, hB, hf⟩ := h
  refine ⟨hk, hB, fun B hB' => ?_⟩
  obtain ⟨t'', hr, hst⟩ := hf B hB'
  rw [withBytes_pushC, step_pushC]
  cases hs : Clif.step env p (withBytes s B) with
  | next s2 =>
    rw [hs] at hr
    simp only [res, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, hb⟩ := hr
    refine ⟨.run (pushC ext s2), congrArg (fun b => some (TState.run (pushC ext s2), b)) hb, ?_⟩
    show TState.run (pushC ext (withBytes s2 fun _ => none)) =
      TState.run (pushC ext (withBytes s' fun _ => none))
    rw [withBytes_strip hst]
  | done vals mem =>
    rw [hs] at hr
    simp only [res, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    cases hst
  | trapped c => rw [hs] at hr; simp [res] at hr
  | stuck m => rw [hs] at hr; simp [res] at hr

/-- **A CLIF run, lifted below extra callers**: all its steps but a last one to `.ret` (an
event-free return of the bottom frame). -/
theorem crun_pushC {env p ext} : ∀ {s : Clif.State} {trS} {t : TState},
    CRun env p (.run s) trS t →
    ∃ trS' t', CRun env p (.run (pushC ext s)) trS' t' ∧ trS' <+: trS ∧
      (∀ e ∈ trS.drop trS'.length, e = []) ∧ trS.length ≤ trS'.length + 1 ∧
      (∀ s', t = .run s' → t' = .run (pushC ext s') ∧ trS' = trS) ∧
      (∀ v, t = .ret v → ∃ s', t' = .run (pushC ext s') ∧ CStep env p (.run s') [] (.ret v))
  | s, _, _, .nil =>
    ⟨[], .run (pushC ext s), .nil, List.nil_prefix, by simp, by simp,
      fun s' h => by cases h; exact ⟨rfl, rfl⟩, fun _ h => by cases h⟩
  | s, _, _, .cons (t' := t1) hs r => by
    cases t1 with
    | run s1 =>
      obtain ⟨trS', t', hr', hp, hd, hl, hrun, hret⟩ := crun_pushC r
      refine ⟨_ :: trS', t', .cons (cstep_pushC hs) hr', (List.prefix_cons_inj _).2 hp,
        by simpa using hd, by simp; omega, fun s' h => ?_, hret⟩
      obtain ⟨h1, h2⟩ := hrun s' h
      exact ⟨h1, by rw [h2]⟩
    | ret v =>
      cases r with
      | nil =>
        refine ⟨[], .run (pushC ext s), .nil, List.nil_prefix, ?_, by simp, ?_, ?_⟩
        · simpa using cstep_ret_nil hs
        · intro _ h; cases h
        · intro _ e
          cases e
          have h0 := cstep_ret_nil hs
          subst h0
          exact ⟨s, rfl, hs⟩
      | cons h2 _ => exact (h2 : False).elim

end Concurrency.ClifLift

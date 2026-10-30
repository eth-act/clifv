import FV.Concurrency.ClifCStep

/-!
# CLIF thread steps without events, CLIF thread runs (T2h, #311, layer 2e)

`ClifCStep` gives the `ClifThread.CStep` of the memory statements. This file adds the steps
without events of layer 2's scope and the runs:

* `cstep_pure`: a pure statement (`pureInst`: its outcome is the same on every memory);
* `cstep_branch`, `cstep_ret`: a branch (`jump`, `brif`, `br_table`) and a return (of the
  outermost activation) neither read nor write bytes;
* `CRun`: runs of `CStep`; `Done t`: the thread has no step (returned, trapped, undefined
  behaviour on every byte memory); `done_of_step`: a statement of the scope whose step is not
  `next` (on the thread's own bytes) has no step at all, since `CStep` steps on every agreeing
  memory, in particular on the thread's.
-/

namespace Concurrency.ClifCStepTerm

open Prog ClifThread IselClif ClifCStep Backend.Proof Backend.Proof.Driver

/-- **Runs of the CLIF thread semantics.** -/
inductive CRun (env : Clif.Env) (p : Clif.Program) :
    TState → List (List (Ev SKind BVal)) → TState → Prop
  | nil {t} : CRun env p t [] t
  | cons {t t' t'' e tr} : CStep env p t e t' → CRun env p t' tr t'' → CRun env p t (e :: tr) t''

theorem CRun.append {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' t'' : TState} {a b : List (List (Ev SKind BVal))},
      CRun env p t a t' → CRun env p t' b t'' → CRun env p t (a ++ b) t''
  | _, _, _, [], _, .nil, h => h
  | _, _, _, _ :: _, _, .cons h1 r, h => .cons h1 (r.append h)

theorem evShape_len (s : Clif.State) : ∀ l ∈ evShape s, l.length ≤ 2 := by
  intro l hl
  unfold evShape at hl
  split at hl
  · split at hl <;> simp at hl <;> (try rcases hl with rfl | rfl) <;> (try subst hl) <;> simp
  · simp at hl; subst hl; simp

theorem cstep_len {env : Clif.Env} {p : Clif.Program} {t t' : TState}
    {evs : List (Ev SKind BVal)} (h : CStep env p t evs t') : evs.length ≤ 2 := by
  cases t with
  | ret _ => exact h.elim
  | run s =>
    have := evShape_len s _ h.1.1
    simpa using this

theorem CRun.length_le {env : Clif.Env} {p : Clif.Program} :
    ∀ {t t' : TState} {tr : List (List (Ev SKind BVal))}, CRun env p t tr t' →
      ∀ j (h : j < tr.length), tr[j].length ≤ 2
  | _, _, _, .nil, j, h => absurd h (Nat.not_lt_zero _)
  | _, _, _, .cons hs r, j, h => by
    cases j with
    | zero => exact cstep_len hs
    | succ j => exact r.length_le j (by simpa using h)

/-- **The thread has no step.** -/
def Done (env : Clif.Env) (p : Clif.Program) (t : TState) : Prop :=
  ¬ ∃ evs t', CStep env p t evs t'

theorem withBytes_self (s : Clif.State) : withBytes s s.mem.bytes = s := rfl

/-- A step without events is a step of `Clif.step` on the thread's own bytes. -/
theorem step_of_cstep_nil {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {t' : TState}
    (h : CStep env p (.run s) [] t') : ∃ t'' B, res (Clif.step env p s) = some (t'', B) := by
  obtain ⟨-, -, hf⟩ := h
  obtain ⟨t'', h1, -⟩ := hf s.mem.bytes trivial
  exact ⟨t'', _, by rw [← withBytes_self s]; exact h1⟩

/-- Statements and terminators of the scope without memory events have only steps without
events. -/
theorem cstep_nil_of_shape {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {evs : List (Ev SKind BVal)} {t' : TState} (hsh : evShape s = [[]])
    (h : CStep env p (.run s) evs t') : evs = [] := by
  have := h.1.1
  rw [hsh] at this
  simpa using this

/-- **A thread whose step on its own bytes fails has none** (no memory events). -/
theorem done_of_step {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (hsh : evShape s = [[]]) (hn : res (Clif.step env p s) = none) : Done env p (.run s) := by
  rintro ⟨evs, t', h⟩
  have e := cstep_nil_of_shape hsh h
  subst e
  obtain ⟨t'', B, h'⟩ := step_of_cstep_nil h
  rw [hn] at h'; cases h'

/-! ## Steps without events -/

theorem evShape_pure {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (hb : s.frame.body = stm :: rest) (hp : pureInst stm.inst = true) : evShape s = [[]] := by
  unfold evShape
  rw [hb]
  simp only
  cases h : stm.inst <;> rw [h] at hp <;> simp [pureInst] at hp <;> rfl

theorem evShape_term {s : Clif.State} (hb : s.frame.body = []) : evShape s = [[]] := by
  unfold evShape
  rw [hb]

/-- **A pure statement steps without events.** -/
theorem cstep_pure {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest) (hp : pureInst stm.inst = true)
    {s' : Clif.State} (hs : Clif.step env p s = .next s') : CStep env p (.run s) [] (.run s') := by
  have hc : ∀ fn args, stm.inst ≠ .call fn args := fun fn args h => by
    rw [h] at hp; simp [pureInst] at hp
  have hci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args := fun _ _ _ h => by
    rw [h] at hp; simp [pureInst] at hp
  obtain ⟨vals, m, hev⟩ := eval_of_step hb hc hci hs
  obtain ⟨-, hall⟩ := evalInst_pure hp hev
  refine cstep_of_eval (evs := []) (vals := vals) (m0 := s.mem) hb hc hci
    ⟨by rw [evShape_pure hb hp]; simp, fun _ h => nomatch h⟩ trivial (fun B _ => ?_) hs
  rw [hall]
  rfl

theorem withB_free (m : Clif.Mem) (B : Bytes) (bases : List Nat) :
    (withB m B).free bases = withB (m.free bases) B := rfl

theorem withB_leave (m : Clif.Mem) (B : Bytes) : (withB m B).leave = withB m.leave B := by
  unfold Clif.Mem.leave
  cases m.place <;> rfl

/-- **A branch or a return of the outermost activation steps without events.** -/
theorem cstep_term {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    (hb : s.frame.body = []) (hcall : s.callers = [])
    (ht : ∀ fn args, s.frame.term ≠ .returnCall fn args)
    (htry : s.frame.term.isTry = false) {t : TState}
    (hs : res (Clif.step env p s) = some (t, s.mem.bytes)) : CStep env p (.run s) [] t := by
  refine ⟨⟨by rw [evShape_term hb]; simp, fun _ h => nomatch h⟩, ⟨s.mem.bytes, trivial⟩,
    fun B _ => ?_⟩
  have hbB : (withBytes s B).frame.body = [] := hb
  rw [Clif.step_term env p _ hbB]
  rw [Clif.step_term env p _ hb] at hs
  show ∃ t'', res (Clif.stepTerm env p (withBytes s B) s.frame.term) = some (t'', B) ∧
    strip t'' = strip t
  cases hT : s.frame.term with
  | jump dest =>
    rw [hT] at hs
    simp only [Clif.stepTerm] at hs ⊢
    cases he : Clif.enterBlock s.frame dest with
    | ok fr =>
      rw [he] at hs
      simp only [Clif.StepResult.ofRes_ok, res, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      refine ⟨.run { s with frame := fr, mem := withB s.mem B }, ?_, rfl⟩
      show res (Clif.StepResult.ofRes (Clif.enterBlock s.frame dest) _) = _
      rw [he]; rfl
    | trap c => rw [he] at hs; cases hs
    | stuck m => rw [he] at hs; cases hs
  | brif c t' e =>
    rw [hT] at hs
    simp only [Clif.stepTerm] at hs ⊢
    cases hg : s.frame.get c with
    | ok cv =>
      rw [hg] at hs
      simp only [Clif.StepResult.ofRes_ok] at hs
      cases he : Clif.enterBlock s.frame (if Clif.Sem.truthy cv.bits then t' else e) with
      | ok fr =>
        rw [he] at hs
        simp only [Clif.StepResult.ofRes_ok, res, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        refine ⟨.run { s with frame := fr, mem := withB s.mem B }, ?_, rfl⟩
        show res (Clif.StepResult.ofRes (s.frame.get c) _) = _
        rw [hg]
        simp only [Clif.StepResult.ofRes_ok]
        show res (Clif.StepResult.ofRes (Clif.enterBlock s.frame _) _) = _
        rw [he]; rfl
      | trap c => rw [he] at hs; cases hs
      | stuck m => rw [he] at hs; cases hs
    | trap c => rw [hg] at hs; cases hs
    | stuck m => rw [hg] at hs; cases hs
  | brTable x d tbl =>
    rw [hT] at hs
    simp only [Clif.stepTerm] at hs ⊢
    cases hg : s.frame.get x with
    | ok xv =>
      rw [hg] at hs
      simp only [Clif.StepResult.ofRes_ok] at hs
      cases he : Clif.enterBlock s.frame (tbl[xv.toNat]?.getD d) with
      | ok fr =>
        rw [he] at hs
        simp only [Clif.StepResult.ofRes_ok, res, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        refine ⟨.run { s with frame := fr, mem := withB s.mem B }, ?_, rfl⟩
        show res (Clif.StepResult.ofRes (s.frame.get x) _) = _
        rw [hg]
        simp only [Clif.StepResult.ofRes_ok]
        show res (Clif.StepResult.ofRes (Clif.enterBlock s.frame _) _) = _
        rw [he]; rfl
      | trap c => rw [he] at hs; cases hs
      | stuck m => rw [he] at hs; cases hs
    | trap c => rw [hg] at hs; cases hs
    | stuck m => rw [hg] at hs; cases hs
  | ret xs =>
    rw [hT] at hs
    simp only [Clif.stepTerm] at hs ⊢
    cases hg : s.frame.getMany xs with
    | ok vals =>
      rw [hg] at hs
      simp only [Clif.StepResult.ofRes_ok, Clif.returnValues] at hs ⊢
      cases hc : Clif.checkTys s!"return values of %{s.frame.func.name}" vals
          (Clif.AbiParam.tys s.frame.func.sig.returns) with
      | ok u =>
        rw [hc] at hs
        simp only [Clif.StepResult.ofRes_ok, hcall, res, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, -⟩ := hs
        refine ⟨.ret vals, ?_, rfl⟩
        show res (Clif.StepResult.ofRes (s.frame.getMany xs) _) = _
        rw [hg]
        show res (Clif.returnValues (withBytes s B) vals (withBytes s B).mem) = _
        simp only [Clif.returnValues]
        rw [show (withBytes s B).frame = s.frame from rfl,
          show (withBytes s B).callers = s.callers from rfl, hc, hcall]
        simp only [Clif.StepResult.ofRes_ok, res, withBytes, withB_free, withB_leave]
      | trap c => rw [hc] at hs; cases hs
      | stuck m => rw [hc] at hs; cases hs
    | trap c => rw [hg] at hs; cases hs
    | stuck m => rw [hg] at hs; cases hs
  | returnCall fn args => exact absurd hT (ht fn args)
  | trap c => rw [hT] at hs; cases hs
  | tryCall fn args et => rw [hT] at htry; cases htry
  | tryCallIndirect callee args et => rw [hT] at htry; cases htry

end Concurrency.ClifCStepTerm

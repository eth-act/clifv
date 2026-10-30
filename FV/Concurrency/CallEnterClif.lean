import FV.Concurrency.ClifThreadI
import FV.Concurrency.ClifLift

/-!
# The callee entry on the CLIF side (#473, step (2))

At a direct `call` of a program function, `Clif.step` enters the callee: the caller's frame (its
block's rest, the call's results) is pushed as the bottom of the callee's caller stack, and the
callee runs from a state with no callers of its own (`ClifLift.pushC`).

* **`step_call_entry`**: the entered state is `pushC ext cs`, where `cs` is the callee's own
  entry state with exactly the facts `CallRetsN.arm_isel_refines_entryCRN` asks of its CLIF
  start (no callers, the callee's function, slots and memory from `Clif.enterSlots`, entry
  block, registers from the argument values, their types), and the argument values are the
  caller's values of the call's uses;
* **`cstepI_call_entry`**: the same step as a `CStepI` step adding the placed slot bytes to the
  mask (`ClifThreadI.cstepI_call`).
-/

namespace Concurrency.CallEnterClif

open Prog ClifThread ClifThreadI

/-- **The callee's CLIF entry state of a direct call** (module doc). -/
theorem step_call_entry {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {results : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    {ext : Clif.ExtFunc} {callee : Clif.Function} (he : s.frame.func.extern? fn = some ext)
    (hc : p.func? ext.name = some callee) (hs : Clif.step env p s = .next s') :
    ∃ vals B0 cs, s.frame.getMany args = .ok vals ∧ callee.blocks[0]? = some B0 ∧
      s' = ClifLift.pushC (({ s.frame with body := rest }, results) :: s.callers) cs ∧
      cs.callers = [] ∧ cs.frame.func = callee ∧
      cs.frame.slots = (Clif.enterSlots callee s.mem).1 ∧
      cs.mem = (Clif.enterSlots callee s.mem).2 ∧
      cs.frame.body = B0.body ∧ cs.frame.term = B0.term ∧
      Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some cs.frame.regs ∧
      vals.map (·.ty) = B0.params.map (·.2) ∧ vals.map (·.ty) = callee.sig.params.map (·.ty) := by
  rw [Clif.step_call env p s rest results fn args hb] at hs
  unfold Clif.stepCall at hs
  simp only [he, Clif.Res.ofOption] at hs
  cases hg : s.frame.getMany args with
  | trap c => rw [hg] at hs; simp [Clif.StepResult.ofRes] at hs
  | stuck m => rw [hg] at hs; simp [Clif.StepResult.ofRes] at hs
  | ok vals =>
    rw [hg] at hs
    rcases Bool.eq_false_or_eq_true (vals.map (·.ty) == Clif.AbiParam.tys ext.sig.params) with h1 | h1
    · simp only [Clif.Res.ok_bind, Clif.checkTys, h1, Clif.Res.check_true, Clif.StepResult.ofRes,
        hc, Clif.Res.pure_eq] at hs
      split at hs
      · cases hf : Clif.enterFunc callee vals s.mem with
        | trap c => rw [hf] at hs; cases hs
        | stuck m => rw [hf] at hs; cases hs
        | ok fm =>
          rw [hf] at hs
          cases hs
          unfold Clif.enterFunc at hf
          rcases Bool.eq_false_or_eq_true
            (vals.map (·.ty) == Clif.AbiParam.tys callee.sig.params) with h3 | h3
          · simp only [Clif.checkTys, h3, Clif.Res.check_true, Clif.Res.ok_bind] at hf
            cases hen : callee.entry? with
            | none => simp [hen, Clif.Res.ofOption] at hf
            | some B0 =>
              simp only [hen, Clif.Res.ofOption_some, Clif.Res.ok_bind] at hf
              rcases Bool.eq_false_or_eq_true (vals.map (·.ty) == B0.params.map (·.2)) with h4 | h4
              · simp only [Clif.checkTys, h4, Clif.Res.check_true, Clif.Res.ok_bind] at hf
                cases hr : Clif.Regs.empty.setMany (B0.params.map (·.1)) vals with
                | none => simp [hr, Clif.Res.ofOption] at hf
                | some regs =>
                  simp only [hr, Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.pure_eq] at hf
                  cases hf
                  refine ⟨vals, B0,
                    { frame := { func := callee, regs := regs,
                                 slots := (Clif.enterSlots callee s.mem).fst,
                                 body := B0.body, term := B0.term }
                      callers := []
                      mem := (Clif.enterSlots callee s.mem).snd },
                    rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hr, by simpa using h4,
                    by simpa [Clif.AbiParam.tys] using h3⟩
                  simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hen
              · simp [Clif.checkTys, Clif.Res.check_false, Clif.Res.stuck_bind, Clif.Res.ok_bind, h4] at hf
          · simp [Clif.checkTys, Clif.Res.check_false, Clif.Res.stuck_bind, Clif.Res.ok_bind, h3] at hf
      · simp at hs
    · simp [Clif.checkTys, Clif.Res.check_false, Clif.Res.stuck_bind, Clif.Res.ok_bind, h1, Clif.StepResult.ofRes] at hs

/-- **The callee entry as a `CStepI` step** (module doc): the step to `pushC ext cs` adds the
callee's placed slot bytes to the mask. -/
theorem cstepI_call_entry {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {results : List Clif.ValueId} {fn : Clif.FnRef} {args : List Clif.ValueId}
    {rest : List Clif.Stmt} (hb : s.frame.body = { results, inst := .call fn args } :: rest)
    {ext : Clif.ExtFunc} {callee : Clif.Function} (he : s.frame.func.extern? fn = some ext)
    (hc : p.func? ext.name = some callee) (hs : Clif.step env p s = .next s') (U : Nat → Prop)
    (hi : ∀ pl, s.mem.place = some pl → pl.init = none) :
    ∃ vals B0 cs, s.frame.getMany args = .ok vals ∧ callee.blocks[0]? = some B0 ∧
      CStepI env p (.run s, U) []
        (.run (ClifLift.pushC (({ s.frame with body := rest }, results) :: s.callers) cs),
          fun a => U a ∨ slotZ callee s.mem a) ∧
      cs.callers = [] ∧ cs.frame.func = callee ∧
      cs.frame.slots = (Clif.enterSlots callee s.mem).1 ∧
      cs.mem = (Clif.enterSlots callee s.mem).2 ∧
      cs.frame.body = B0.body ∧ cs.frame.term = B0.term ∧
      Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some cs.frame.regs ∧
      vals.map (·.ty) = B0.params.map (·.2) ∧ vals.map (·.ty) = callee.sig.params.map (·.ty) := by
  obtain ⟨vals, B0, cs, h1, h2, e, h3⟩ := step_call_entry hb he hc hs
  exact ⟨vals, B0, cs, h1, h2, e ▸ cstepI_call hb he hc hs U hi, h3⟩

end Concurrency.CallEnterClif

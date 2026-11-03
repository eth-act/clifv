import FV.E2E.MemTrapStatement

namespace E2E.MemoryFaultSource
open Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Source reachability composes without a condition on the intervening effects. -/
theorem reach_append {env : Clif.Env} {p : Clif.Program} {first middle last : Clif.State}
    (before : Reach env p first middle) (suffix : Reach env p middle last) :
    Reach env p first last := by
  induction before generalizing last with
  | refl => exact suffix
  | step stepped path ih => exact .step stepped (ih suffix)

/-- A mapping fact holds at every source state reached from its original entry. -/
theorem mapFaults_of_reach {mp : ArmFault.MemMap} {env : Clif.Env} {p : Clif.Program}
    {first next : Clif.State} (mapped : MapFaults mp env p first)
    (before : Reach env p first next) : MapFaults mp env p next := by
  intro state code address bytes reached event
  exact mapped state code address bytes (reach_append before reached) event

/-- A real access trap depends on the frame and memory, including the original flags.
The caller stack, environment, and program view do not alter that access event. -/
theorem memTrapAt_transport {env env' : Clif.Env} {p p' : Clif.Program}
    {source target : Clif.State} {code : Clif.TrapCode} {address bytes : Nat}
    (frame : target.frame = source.frame) (memory : target.mem = source.mem)
    (event : Clif.MemTrapAt env p source code address bytes) :
    Clif.MemTrapAt env' p' target code address bytes := by
  obtain ⟨stepped,invalid,st,rest,body,access⟩ := event
  have noCall : ∀ fn args, st.inst ≠ .call fn args := by
    intro fn args equal
    rw [equal] at access
    cases access
  have noIndirect : ∀ sig callee args, st.inst ≠ .callIndirect sig callee args := by
    intro sig callee args equal
    rw [equal] at access
    cases access
  have evaluation : Clif.evalInst source.frame source.mem st.inst = .trap code := by
    rw [Clif.step_inst env p source st rest body noCall noIndirect] at stepped
    cases evaluated : Clif.evalInst source.frame source.mem st.inst with
    | ok value =>
      rw [evaluated] at stepped
      simp only [Clif.StepResult.ofRes,Clif.continueWith] at stepped
      split at stepped <;> cases stepped
    | stuck message => rw [evaluated] at stepped; cases stepped
    | trap actual => rw [evaluated] at stepped; cases stepped; rfl
  have movedBody : target.frame.body = st :: rest := by rw [frame]; exact body
  refine ⟨?_,?_,st,rest,movedBody,?_⟩
  · rw [Clif.step_inst env' p' target st rest movedBody noCall noIndirect]
    rw [frame,memory,evaluation]
    rfl
  · rw [memory]
    exact invalid
  · simpa only [frame] using access

/-- An internally proved source simulation transfers the original mapping fact.
The final program theorem must derive this reachability relation itself. -/
theorem mapFaults_of_reach_simulation {mp : ArmFault.MemMap}
    {env env' : Clif.Env} {p p' : Clif.Program} {first target : Clif.State}
    (mapped : MapFaults mp env p first)
    (simulation : ∀ state, Reach env' p' target state →
      ∃ original, Reach env p first original ∧
        original.frame = state.frame ∧ original.mem = state.mem) :
    MapFaults mp env' p' target := by
  intro state code address bytes reached event
  obtain ⟨original,path,frame,memory⟩ := simulation state reached
  exact mapped original code address bytes path (memTrapAt_transport frame memory event)

end E2E.MemoryFaultSource

import FV.Backend.Proof.StockFenceMachine

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- An ordinary return body does not consult the external environment or program.
The proof retains every source outcome, including memory faults and zero division. -/
theorem ordinary_run_environment {env env' : Clif.Env} {cp cp' : Clif.Program}
    (fuel : Nat) (state : Clif.State)
    (ordinary : ∀ stm ∈ state.frame.body,OrdinaryBody.OrdinaryInst stm.inst)
    (callers : state.callers = []) {returns : List Nat} (terminal : state.frame.term = .ret returns) :
    Clif.runLoop env cp fuel state = Clif.runLoop env' cp' fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases body : state.frame.body with
    | nil =>
      rw [Clif.runLoop_succ,Clif.runLoop_succ,Clif.step_term env cp state body,
        Clif.step_term env' cp' state body,terminal]
      simp only [Clif.stepTerm]
      cases evaluated : state.frame.getMany returns with
      | trap code => rfl
      | stuck message => rfl
      | ok values =>
        simp only [Clif.StepResult.ofRes,Clif.returnValues,callers]
        cases Clif.checkTys s!"return values of %{state.frame.func.name}" values
          (Clif.AbiParam.tys state.frame.func.sig.returns) <;> rfl
    | cons stm rest =>
      have family := ordinary stm (by rw [body]; exact List.mem_cons_self)
      rw [Clif.runLoop_succ,Clif.runLoop_succ,
        Clif.step_inst env cp state stm rest body family.1 family.2,
        Clif.step_inst env' cp' state stm rest body family.1 family.2]
      cases evaluated : Clif.evalInst state.frame state.mem stm.inst with
      | trap code => rfl
      | stuck message => rfl
      | ok value =>
        obtain ⟨values,mem⟩ := value
        simp only [Clif.StepResult.ofRes]
        unfold Clif.continueWith
        cases assigned : state.frame.regs.setMany stm.results values with
        | none => rfl
        | some regs =>
          simp only
          apply ih
          · intro next member
            exact ordinary next (by rw [body]; exact List.mem_cons_of_mem stm member)
          · exact callers
          · exact terminal

end Backend.Stock.Proof.MemoryFaults

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver E2E MemoryFaults
set_option autoImplicit false
set_option Elab.async false

/-- The unchanged original mixed function has the same run in both source program views. -/
theorem mixed_source_environment {env env' : Clif.Env} {cp cp' : Clif.Program}
    {args : List Clif.Val} {state : Clif.State} (entered : ClifEntry function args state) (fuel : Nat) :
    Clif.runLoop env cp fuel state = Clif.runLoop env' cp' fuel state := by
  obtain ⟨block,entry,body,term,types,regs⟩ := entered.entry
  have same : block = function.blocks[0]! := by
    simpa [Clif.Function.entry?,function] using entry.symm
  subst block
  apply ordinary_run_environment fuel state _ entered.callers (term.trans rfl)
  intro stm member
  rw [body] at member
  simp [function] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [OrdinaryBody.OrdinaryInst]

end Backend.Stock.Proof.FenceFixture

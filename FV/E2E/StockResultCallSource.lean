import FV.Backend.StockResultCallCheck
import FV.Backend.Proof.StockDirectCallResult
import FV.Backend.Proof.StockMemoryNotrap

namespace Backend.Stock.ResultCall
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem result_return_run {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {fuel : Nat} {values : List Clif.Val} {source : Nat}
    {value : Clif.Val} {result : Clif.AbiParam}
    (body : fr.body = []) (term : fr.term = .ret [source])
    (returns : fr.func.sig.returns = [result]) (read : fr.getMany [source] = .ok [value])
    (typed : value.ty = result.ty)
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    values = [value] ∧ outMem = (cm.free (fr.slots.map (·.2))).leave := by
  have step : Clif.step env cp ⟨fr,[],cm⟩ =
      .done [value] (cm.free (fr.slots.map (·.2))).leave := by
    simp [Clif.step,body,term,Clif.stepTerm,read,Clif.returnValues,returns,typed,
      Clif.AbiParam.tys,Clif.checkTys,Clif.Res.check,Clif.StepResult.ofRes]
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,step] at returned
    cases returned
    exact ⟨rfl,rfl⟩

/-- The complete original source run supplies the scalar callback result and its actual memory effect. -/
theorem source_return_call {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {fuel : Nat} {values : List Clif.Val}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} {source : Nat} {result : Clif.AbiParam}
    (body : fr.body = [⟨[source],.call fn args⟩]) (term : fr.term = .ret [source])
    (returns : fr.func.sig.returns = [result]) (lookup : fr.func.extern? fn = some ext)
    (external : cp.func? ext.name = none) (calleeReturns : ext.sig.returns = [result])
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (arguments : List Clif.Val)
      (after : Clif.Mem) (value : Clif.Val),
      env.extern ext.name = some g ∧ fr.getMany args = .ok arguments ∧
      arguments.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧
      g arguments cm = .returned [value] after ∧ value.ty = result.ty ∧ values = [value] ∧
      outMem = (after.free (fr.slots.map (·.2))).leave := by
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    have step : Clif.step env cp ⟨fr,[],cm⟩ =
        Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
          (fun pair => Clif.continueWith ⟨fr,[],cm⟩ [] [source] pair.1 pair.2) := by
      simp only [Clif.step,body]
      apply stepCall_eq
      intro e found
      have same : e = ext := Option.some.inj (found.symm.trans lookup)
      subst e
      exact external
    rw [Clif.runLoop_succ,step] at returned
    cases outcome : instOutcome env cp fr cm (.call fn args) with
    | trap code => simp only [outcome,Clif.StepResult.ofRes] at returned; cases returned
    | stuck message => simp only [outcome,Clif.StepResult.ofRes] at returned; cases returned
    | ok pair =>
      obtain ⟨results,after⟩ := pair
      obtain ⟨e,arguments,g,found,read,types,called,run,retTypes⟩ := instOutcome_call_ok outcome
      have same : e = ext := Option.some.inj (found.symm.trans lookup)
      subst e
      have count : results.length = 1 := by
        simpa only [calleeReturns,Clif.AbiParam.tys,List.length_map,List.length_cons,List.length_nil]
          using congrArg List.length retTypes
      cases results with
      | nil => cases count
      | cons value tail =>
        have empty : tail = [] := by simpa using count
        subst tail
        have typed : value.ty = result.ty := by
          simpa only [calleeReturns,Clif.AbiParam.tys,List.map_cons,List.map_nil,List.cons.injEq,and_true]
            using retTypes
        simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at returned
        have get : ({fr with regs := fr.regs.set source value,body := []} : Clif.Frame).getMany [source] =
            .ok [value] := by
          simp [Clif.Frame.getMany,Clif.Frame.get,Clif.Regs.set,Clif.Res.ofOption]
        obtain ⟨equal,memory⟩ := result_return_run (fr := {fr with regs := fr.regs.set source value,body := []})
          rfl term returns get typed returned
        exact ⟨g,arguments,after,value,called,read,types,run,typed,equal,memory⟩

end Backend.Stock.ResultCall

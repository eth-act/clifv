import FV.Backend.Proof.StockLiveCallArithmetic
import FV.Backend.Proof.StockMemoryNotrap

namespace Backend.Stock.Proof.LiveCallArithmetic
open Backend Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- A successful original run exposes its actual call result, arbitrary memory effect, and remaining source run. -/
theorem source_call_continues {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {rest : List Clif.Stmt} {fuel : Nat} {values : List Clif.Val}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} {source : Nat} {result : Clif.AbiParam}
    (body : fr.body = ⟨[source],.call fn args⟩ :: rest)
    (lookup : fr.func.extern? fn = some ext) (external : cp.func? ext.name = none)
    (returns : ext.sig.returns = [result])
    (returned : Clif.runLoop env cp (fuel+1) ⟨fr,[],cm⟩ = .returned values outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (arguments : List Clif.Val)
      (after : Clif.Mem) (value : Clif.Val),
      env.extern ext.name = some g ∧ fr.getMany args = .ok arguments ∧
      arguments.map (·.ty) = Clif.AbiParam.tys ext.sig.params ∧
      g arguments cm = .returned [value] after ∧ value.ty = result.ty ∧
      Clif.runLoop env cp fuel ⟨{fr with regs := fr.regs.set source value,body := rest},[],after⟩ =
        .returned values outMem := by
  have step : Clif.step env cp ⟨fr,[],cm⟩ =
      Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
        (fun pair => Clif.continueWith ⟨fr,[],cm⟩ rest [source] pair.1 pair.2) := by
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
      simpa only [returns,Clif.AbiParam.tys,List.length_map,List.length_cons,List.length_nil]
        using congrArg List.length retTypes
    cases results with
    | nil => cases count
    | cons value tail =>
      have empty : tail = [] := by simpa using count
      subst tail
      have typed : value.ty = result.ty := by
        simpa only [returns,Clif.AbiParam.tys,List.map_cons,List.map_nil,List.cons.injEq,and_true]
          using retTypes
      simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at returned
      exact ⟨g,arguments,after,value,called,read,types,run,typed,returned⟩

/-- Binding the returned value preserves the distinct original parameter before arithmetic uses it. -/
theorem continued_live {fr : Clif.Frame} {source live : Nat} (separate : live ≠ source)
    {returned value : Clif.Val} (read : fr.regs live = some value) (rest : List Clif.Stmt) :
    ({fr with regs := fr.regs.set source returned,body := rest} : Clif.Frame).regs live = some value := by
  simpa only [Clif.Regs.set,separate,↓reduceIte] using read

/-- The remaining source addition returns its exact two words and frees only the original caller slots. -/
theorem source_add_returns {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {called live sum fuel : Nat} {u v : BitVec 64} {values : List Clif.Val}
    (body : fr.body = [⟨[sum],.binary .iadd .i64 called live⟩]) (term : fr.term = .ret [sum])
    (returns : fr.func.sig.returns.map (·.ty) = [.i64])
    (readCalled : fr.regs called = some ⟨.i64,u⟩) (readLive : fr.regs live = some ⟨.i64,v⟩)
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    values = [⟨.i64,u+v⟩] ∧ outMem = (cm.free (fr.slots.map (·.2))).leave := by
  have evaluated : Clif.evalInst fr cm (.binary .iadd .i64 called live) = .ok ([⟨.i64,u+v⟩],cm) := by
    simp [Clif.evalInst,Clif.Frame.getAs,Clif.Frame.get,readCalled,readLive,Clif.Res.ofOption,
      Clif.Val.as?,Clif.BinaryOp.isShift,Clif.Sem.binary,Clif.Sem.iadd]
  let next : Clif.Frame := {fr with regs := fr.regs.set sum ⟨.i64,u+v⟩,body := []}
  have first : Clif.step env cp ⟨fr,[],cm⟩ = .next ⟨next,[],cm⟩ := by
    simp [Clif.step,body,evaluated,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany,next]
  have last : Clif.step env cp ⟨next,[],cm⟩ =
      .done [⟨.i64,u+v⟩] (cm.free (fr.slots.map (·.2))).leave := by
    simp [Clif.step,next,term,Clif.stepTerm,Clif.Frame.getMany,Clif.Frame.get,Clif.Regs.set,
      Clif.Res.ofOption,Clif.returnValues,Clif.checkTys,Clif.AbiParam.tys,returns,Clif.Res.check,
      Clif.StepResult.ofRes]
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,first] at returned
    cases fuel with
    | zero => cases returned
    | succ fuel =>
      rw [Clif.runLoop_succ,last] at returned
      cases returned
      exact ⟨rfl,rfl⟩

end Backend.Stock.Proof.LiveCallArithmetic

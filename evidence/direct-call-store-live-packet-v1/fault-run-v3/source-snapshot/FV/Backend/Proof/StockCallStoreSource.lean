import FV.Backend.Proof.StockCallStoreResult
import FV.Backend.Proof.StockLiveCallSource

namespace Backend.Stock.Proof.CallStoreResult
open Backend Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- A successful source store retains the call result and returns the actual updated memory. -/
theorem source_store_returns {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm outMem : Clif.Mem} {value pointer fuel : Nat} {word : BitVec 64}
    {flags : Clif.MemFlags} {outputs : List Clif.Val}
    (body : fr.body = [⟨[],.store .store .i64 flags value pointer 8⟩])
    (term : fr.term = .ret [value]) (returns : fr.func.sig.returns.map (·.ty) = [.i64])
    (read : fr.regs value = some ⟨.i64,word⟩) (little : flags.endianness ≠ some .big)
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned outputs outMem) :
    ∃ stored,Clif.evalInst fr cm (.store .store .i64 flags value pointer 8) = .ok ([],stored) ∧
      outputs = [⟨.i64,word⟩] ∧ outMem = (stored.free (fr.slots.map (·.2))).leave := by
  have step := Clif.step_inst env cp ⟨fr,[],cm⟩ ⟨[],.store .store .i64 flags value pointer 8⟩ []
    body (by intro fn args impossible; cases impossible)
    (by intro sig callee args impossible; cases impossible)
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ,step] at returned
    cases evaluated : Clif.evalInst fr cm (.store .store .i64 flags value pointer 8) with
    | trap code => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at returned; cases returned
    | ok pair =>
      obtain ⟨values,stored⟩ := pair
      obtain ⟨bits,pv,readValue,readPointer,size,valid,empty,written⟩ := evalInst_store_inv little evaluated
      subst values
      let next : Clif.Frame := {fr with body := []}
      have remaining : Clif.runLoop env cp fuel ⟨next,[],stored⟩ = .returned outputs outMem := by
        simpa only [evaluated,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] using returned
      have last : Clif.step env cp ⟨next,[],stored⟩ =
          .done [⟨.i64,word⟩] (stored.free (fr.slots.map (·.2))).leave := by
        simp [Clif.step,next,term,Clif.stepTerm,Clif.Frame.getMany,Clif.Frame.get,read,
          Clif.Res.ofOption,Clif.returnValues,Clif.checkTys,Clif.AbiParam.tys,returns,
          Clif.Res.check,Clif.StepResult.ofRes]
      cases fuel with
      | zero => cases remaining
      | succ fuel =>
        rw [Clif.runLoop_succ,last] at remaining
        cases remaining
        exact ⟨stored,rfl,rfl,rfl⟩

/-- A store followed by a return has no later source trap that can hide its first access fault. -/
theorem source_store_faults {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {value pointer fuel : Nat} {flags : Clif.MemFlags} {code : Clif.TrapCode}
    (body : fr.body = [⟨[],.store .store .i64 flags value pointer 8⟩])
    (term : fr.term = .ret [value]) (little : flags.endianness ≠ some .big)
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code) :
    Clif.evalInst fr cm (.store .store .i64 flags value pointer 8) = .trap code := by
  have step := Clif.step_inst env cp ⟨fr,[],cm⟩ ⟨[],.store .store .i64 flags value pointer 8⟩ []
    body (by intro fn args impossible; cases impossible)
    (by intro sig callee args impossible; cases impossible)
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    rw [Clif.runLoop_succ,step] at trapped
    cases evaluated : Clif.evalInst fr cm (.store .store .i64 flags value pointer 8) with
    | trap actual =>
      simp only [evaluated,Clif.StepResult.ofRes] at trapped
      cases trapped
      rfl
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨values,stored⟩ := pair
      obtain ⟨bits,pv,readValue,readPointer,size,valid,empty,written⟩ := evalInst_store_inv little evaluated
      subst values
      have remaining : Clif.runLoop env cp fuel ⟨{fr with body := []},[],stored⟩ = .trapped code := by
        simpa only [evaluated,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] using trapped
      exact False.elim (OrdinaryBody.ordinary_source_notrap fuel
        ⟨{fr with body := []},[],stored⟩ rfl (by intro statement member; cases member) term code remaining)

/-- Keep callee traps explicit and derive the actual post-call continuation for store faults. -/
theorem source_call_fault_or_continues {env : Clif.Env} {cp : Clif.Program} {fr : Clif.Frame}
    {cm : Clif.Mem} {rest : List Clif.Stmt} {fuel : Nat} {code : Clif.TrapCode}
    {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc} {source : Nat} {result : Clif.AbiParam}
    (body : fr.body = ⟨[source],.call fn args⟩ :: rest)
    (lookup : fr.func.extern? fn = some ext) (external : cp.func? ext.name = none)
    (returns : ext.sig.returns = [result])
    (trapped : Clif.runLoop env cp (fuel+1) ⟨fr,[],cm⟩ = .trapped code) :
    instOutcome env cp fr cm (.call fn args) = .trap code ∨
      ∃ (after : Clif.Mem) (value : Clif.Val),
        instOutcome env cp fr cm (.call fn args) = .ok ([value],after) ∧ value.ty = result.ty ∧
        Clif.runLoop env cp fuel ⟨{fr with regs := fr.regs.set source value,body := rest},[],after⟩ =
          .trapped code := by
  have step : Clif.step env cp ⟨fr,[],cm⟩ =
      Clif.StepResult.ofRes (instOutcome env cp fr cm (.call fn args))
        (fun pair => Clif.continueWith ⟨fr,[],cm⟩ rest [source] pair.1 pair.2) := by
    simp only [Clif.step,body]
    apply stepCall_eq
    intro e found
    have same : e = ext := Option.some.inj (found.symm.trans lookup)
    subst e
    exact external
  rw [Clif.runLoop_succ,step] at trapped
  cases outcome : instOutcome env cp fr cm (.call fn args) with
  | trap actual =>
    simp only [outcome,Clif.StepResult.ofRes] at trapped
    cases trapped
    exact .inl rfl
  | stuck message => simp only [outcome,Clif.StepResult.ofRes] at trapped; cases trapped
  | ok pair =>
    obtain ⟨values,after⟩ := pair
    obtain ⟨e,arguments,g,found,read,types,called,run,retTypes⟩ := instOutcome_call_ok outcome
    have same : e = ext := Option.some.inj (found.symm.trans lookup)
    subst e
    have count : values.length = 1 := by
      simpa only [returns,Clif.AbiParam.tys,List.length_map,List.length_cons,List.length_nil]
        using congrArg List.length retTypes
    cases values with
    | nil => cases count
    | cons value tail =>
      have empty : tail = [] := by simpa using count
      subst tail
      have typed : value.ty = result.ty := by
        simpa only [returns,Clif.AbiParam.tys,List.map_cons,List.map_nil,List.cons.injEq,and_true]
          using retTypes
      simp only [outcome,Clif.StepResult.ofRes,Clif.continueWith,Clif.Regs.setMany] at trapped
      exact .inr ⟨after,value,rfl,typed,trapped⟩

end Backend.Stock.Proof.CallStoreResult

import FV.Backend.Proof.StockCallStoreFault
import FV.E2E.StockCallStoreSourceResult
import FV.E2E.Statement

namespace Backend.Stock.CallStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A caller trap is either the original callee trap or the original invalid post-call store. -/
theorem Layout.source_fault {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {env : Clif.Env} {cp : Clif.Program} (subset : InSubset cp f)
    {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code) :
    instOutcome env cp fr cm (.call layout.data.fn [layout.data.argument]) = .trap code ∨
      ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (argument returned : BitVec 64)
        (after : Clif.Mem) (pointer : Clif.Val),
        env.extern layout.data.ext.name = some g ∧
        fr.getMany [layout.data.argument] = .ok [⟨.i64,argument⟩] ∧
        g [⟨.i64,argument⟩] cm = .returned [⟨.i64,returned⟩] after ∧
        fr.regs layout.data.pointer = some pointer ∧ pointer.ty = .i64 ∧
        after.valid (Clif.effAddr pointer 8) 8 = false ∧ layout.data.flags.trapCode = some code := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    pointerCalled,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
  have originalEntry := entered
  obtain ⟨block,regs,found,types,paramTypes,set,frame⟩ := entered
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body' : fr.body = [⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩,
      ⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩] :=
    (congrArg Clif.Frame.body frame).trans body
  have term' : fr.term = .ret [layout.data.called] := (congrArg Clif.Frame.term frame).trans term
  have lookup' : fr.func.extern? layout.data.fn = some layout.data.ext := by rw [func]; exact lookup
  have external : cp.func? layout.data.ext.name = none :=
    subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩ (by simp [body])
      layout.data.fn [layout.data.argument] rfl layout.data.ext lookup
  cases fuel with
  | zero => cases trapped
  | succ fuel =>
    rcases CallStoreResult.source_fault_decomposition pointerCalled body' term'
        (by rw [flags]; decide) lookup' external calleeReturns trapped with callTrap |
        ⟨after,value,bits,pointer,callOk,typed,readValue,pointerRead,invalid,flag⟩
    · exact .inl callTrap
    · obtain ⟨e,arguments,g,extFound,read,argTypes,callee,called,resultTypes⟩ := instOutcome_call_ok callOk
      have same : e = layout.data.ext := Option.some.inj (extFound.symm.trans lookup')
      subst e
      have count : arguments.length = 1 := by simpa using (getMany_ok read).1
      cases arguments with
      | nil => cases count
      | cons original rest =>
        have empty : rest = [] := by simpa using count
        subst rest
        have originalType : original.ty = .i64 := by
          simpa only [Clif.AbiParam.tys,calleeParams,List.map_cons,List.map_nil,List.cons.injEq,and_true] using argTypes
        obtain ⟨argumentTy,argument⟩ := original
        dsimp only at originalType
        subst argumentTy
        obtain ⟨returnedTy,returnedWord⟩ := value
        have returnedType : returnedTy = .i64 := typed.trans integer
        subst returnedTy
        have register : fr.regs layout.data.pointer = some pointer := by
          cases actual : fr.regs layout.data.pointer with
          | none => simp [Clif.Frame.get,actual,Clif.Res.ofOption] at pointerRead
          | some v =>
            have eq : v = pointer := by simpa only [Clif.Frame.get,actual,Clif.Res.ofOption,Clif.Res.ok.injEq] using pointerRead
            subst v
            rfl
        exact .inr ⟨g,argument,returnedWord,after,pointer,callee,read,called,register,
          layout.pointer_type originalEntry register,invalid,flag⟩

end Backend.Stock.CallStore

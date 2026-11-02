import FV.E2E.StockCallStoreLayout
import FV.E2E.Statement

namespace Backend.Stock.CallStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem Layout.pointer_type {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {pointer : Clif.Val} (read : fr.regs layout.data.pointer = some pointer) : pointer.ty = .i64 := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    pointerCalled,argumentCalled,pointerArgument,flags,bytes⟩ := layout.source_fields
  obtain ⟨block,regs,entry,types,paramTypes,set,frame⟩ := entered
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (entry.symm.trans first)
  have noDuplicates : (layout.data.block.params.map (·.1)).Nodup := by
    simp [parameters,pointerArgument]
  have member : layout.data.pointer ∈ layout.data.block.params.map (·.1) := by simp [parameters]
  have register : regs layout.data.pointer = some pointer := by
    simpa only [congrArg Clif.Frame.regs frame] using read
  obtain ⟨parameter,present,key,typed⟩ := setMany_param_ty set noDuplicates paramTypes member register
  simp only [parameters,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl <;> exact typed

/-- The complete original return derives the actual callee effect and successful store internally. -/
theorem Layout.source_result {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {env : Clif.Env} {cp : Clif.Program} (subset : InSubset cp f)
    {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {values : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (argument returned : BitVec 64)
      (after stored : Clif.Mem) (pointer : Clif.Val),
      env.extern layout.data.ext.name = some g ∧
      fr.getMany [layout.data.argument] = .ok [⟨.i64,argument⟩] ∧
      g [⟨.i64,argument⟩] cm = .returned [⟨.i64,returned⟩] after ∧
      fr.regs layout.data.pointer = some pointer ∧ pointer.ty = .i64 ∧
      Clif.evalInst {fr with regs := fr.regs.set layout.data.called ⟨.i64,returned⟩,body := [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩]} after
        (.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8) = .ok ([],stored) ∧
      values = [⟨.i64,returned⟩] ∧ outMem = (stored.free (fr.slots.map (·.2))).leave := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    pointerCalled,argumentCalled,pointerArgument,flags,parameterBytes⟩ := layout.source_fields
  have originalEntry := entered
  obtain ⟨block,regs,found,types,paramTypes,set,frame⟩ := entered
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body' : fr.body = ⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩ ::
      [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩] :=
    (congrArg Clif.Frame.body frame).trans body
  have term' : fr.term = .ret [layout.data.called] := (congrArg Clif.Frame.term frame).trans term
  have lookup' : fr.func.extern? layout.data.fn = some layout.data.ext := by rw [func]; exact lookup
  have external : cp.func? layout.data.ext.name = none :=
    subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.argument]⟩ (by simp [body])
      layout.data.fn [layout.data.argument] rfl layout.data.ext lookup
  cases fuel with
  | zero => cases returned
  | succ fuel =>
    obtain ⟨g,arguments,after,value,callee,read,argTypes,called,typed,tail⟩ :=
      LiveCallArithmetic.source_call_continues body' lookup' external calleeReturns returned
    have count : arguments.length = 1 := by simpa using (getMany_ok read).1
    cases arguments with
    | nil => cases count
    | cons original rest =>
      have empty : rest = [] := by simpa using count
      subst rest
      have originalType : original.ty = .i64 := by
        simpa only [Clif.AbiParam.tys,calleeParams,List.map_cons,List.map_nil,List.cons.injEq,and_true]
          using argTypes
      obtain ⟨argumentTy,argument⟩ := original
      dsimp only at originalType
      subst argumentTy
      obtain ⟨returnedTy,returnedWord⟩ := value
      have returnedType : returnedTy = .i64 := typed.trans integer
      subst returnedTy
      have readResult : (fr.regs.set layout.data.called ⟨.i64,returnedWord⟩) layout.data.called =
          some ⟨.i64,returnedWord⟩ := Clif.Regs.set_same _ _ _
      have little : layout.data.flags.endianness ≠ some .big := by rw [flags]; decide
      obtain ⟨stored,evaluated,outputs,freed⟩ := CallStoreResult.source_store_returns
        (fr := {fr with regs := fr.regs.set layout.data.called ⟨.i64,returnedWord⟩,body := [⟨[],.store .store .i64 layout.data.flags layout.data.called layout.data.pointer 8⟩]})
        rfl term'
        (by change fr.func.sig.returns.map (·.ty) = [.i64]; rw [func]; exact returns)
        readResult little tail
      obtain ⟨bits,pointer,storedValue,pointerRead,size,valid,empty,memory⟩ := evalInst_store_inv little evaluated
      have originalPointer : fr.regs layout.data.pointer = some pointer := by
        simpa only [Clif.Regs.set,pointerCalled,↓reduceIte] using pointerRead
      exact ⟨g,argument,returnedWord,after,stored,pointer,callee,read,called,originalPointer,
        layout.pointer_type originalEntry originalPointer,evaluated,outputs,freed⟩

end Backend.Stock.CallStore

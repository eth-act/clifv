import FV.E2E.StockLiveCallLayout
import FV.E2E.Statement

namespace Backend.Stock.LiveCall
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- The original complete run retains its parameter, consumes the actual call result, and preserves arbitrary callee effects. -/
theorem Layout.source_result {f : Clif.Function} {result : Stock.Result} (layout : Layout f result)
    {env : Clif.Env} {cp : Clif.Program} (subset : InSubset cp f)
    {args : List Clif.Val} {fr : Clif.Frame} {cm outMem : Clif.Mem}
    (entered : SourceEntry f args fr) {fuel : Nat} {values : List Clif.Val}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned values outMem) :
    ∃ (g : List Clif.Val → Clif.Mem → Clif.Outcome) (live returned : BitVec 64) (after : Clif.Mem),
      env.extern layout.data.ext.name = some g ∧
      fr.getMany [layout.data.live] = .ok [⟨.i64,live⟩] ∧
      g [⟨.i64,live⟩] cm = .returned [⟨.i64,returned⟩] after ∧
      values = [⟨.i64,returned+live⟩] ∧ outMem = (after.free (fr.slots.map (·.2))).leave := by
  obtain ⟨blocks,parameters,body,term,params,returns,calleeParams,calleeReturns,integer,lookup,pins,
    separate,sumCalled,sumLive⟩ := layout.source_fields
  obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
  have first : f.entry? = some layout.data.block := by
    simp only [Clif.Function.entry?,blocks,List.head?_cons]
  cases Option.some.inj (found.symm.trans first)
  have func : fr.func = f := congrArg Clif.Frame.func frame
  have body' : fr.body = ⟨[layout.data.called],.call layout.data.fn [layout.data.live]⟩ ::
      [⟨[layout.data.sum],.binary .iadd .i64 layout.data.called layout.data.live⟩] :=
    (congrArg Clif.Frame.body frame).trans body
  have term' : fr.term = .ret [layout.data.sum] := (congrArg Clif.Frame.term frame).trans term
  have lookup' : fr.func.extern? layout.data.fn = some layout.data.ext := by rw [func]; exact lookup
  have external : cp.func? layout.data.ext.name = none :=
    subset.externCalls layout.data.block (by simp [blocks])
      ⟨[layout.data.called],.call layout.data.fn [layout.data.live]⟩ (by simp [body])
      layout.data.fn [layout.data.live] rfl layout.data.ext lookup
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
      obtain ⟨originalTy,live⟩ := original
      dsimp only at originalType
      subst originalTy
      obtain ⟨returnedTy,returnedWord⟩ := value
      have returnType : returnedTy = .i64 := typed.trans integer
      subst returnedTy
      have originalRead : fr.regs layout.data.live = some ⟨.i64,live⟩ :=
        (getMany_ok read).2 0 _ _ rfl rfl
      have liveRead := LiveCallArithmetic.continued_live separate originalRead
        [⟨[layout.data.sum],.binary .iadd .i64 layout.data.called layout.data.live⟩]
        (returned := ⟨.i64,returnedWord⟩)
      have resultRead : (fr.regs.set layout.data.called ⟨.i64,returnedWord⟩) layout.data.called =
          some ⟨.i64,returnedWord⟩ := Clif.Regs.set_same _ _ _
      obtain ⟨outputs,memory⟩ := LiveCallArithmetic.source_add_returns
        (fr := {fr with regs := fr.regs.set layout.data.called ⟨.i64,returnedWord⟩,
          body := [⟨[layout.data.sum],.binary .iadd .i64 layout.data.called layout.data.live⟩]}) rfl term'
        (by change fr.func.sig.returns.map (·.ty) = [.i64]; rw [func]; exact returns)
        resultRead liveRead tail
      exact ⟨g,live,returnedWord,after,callee,read,called,outputs,memory⟩

end Backend.Stock.LiveCall

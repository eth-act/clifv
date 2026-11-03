import FV.Backend.Proof.StockAcquireSelectedEmission

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual retained chunk is one original acquire, with its fresh result bound through final aliases. -/
theorem stock_lower_acquire_selected_chunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (pointerReg dest resultId key : Nat),
      event.ctx.valueReg? R.pointer = some (.vreg pointerReg .int) ∧
      R.rootInfo.results = [resultId] ∧ event.ctx.valueReg? resultId = some (.vreg key .int) ∧
      dest = record.input.base.nextVreg ∧
      record.output.emitted = #[.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int) (.vreg pointerReg .int) R.flags] ∧
      step.results = [[.vreg dest .int]] ∧
      (result.final.alias[key]?).join = some dest ∧ aliasNum result.final.alias key = dest := by
  obtain ⟨R,middle,requested,address,next,bound,copies,sink,request,register,marked,state,root,binding,outputState,outputCode⟩ :=
    stock_lower_acquire_selected_emission run scope dominated events records recorded emitted selectedId
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨pointerReg,addressEq⟩ := mapped.valueReg R.pointer address register
  subst address
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys record.inst R.rootInfo _ R.rootInstalled R.rootSource
  have tysEq : tys = [R.target] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  rw [tysEq] at resultTypes length
  obtain ⟨resultId,results⟩ := List.length_eq_one_iff.mp length
  have resultAt : R.rootInfo.results[0]? = some resultId := by rw [results];rfl
  have typeAt : R.rootInfo.resTys[0]? = some (CTy.ofClif R.target) := by rw [resultTypes];rfl
  have valueType := stock_lower_event_result_type run scope dominated events R.rootInstalled R.rootSource resultAt typeAt
  obtain ⟨key,resultReg⟩ := mapped.typedReg resultId (CTy.ofClif R.target) valueType
  have sinkState := (sink_accepted sink).2.2.2.2
  have requestedBase : requested.base = (scanState record.input record.inst).base := by rw [marked,sinkState];rfl
  have fresh : requested.base.nextVreg = record.input.base.nextVreg := by
    rw [requestedBase]
    simp only [scanState]
    split <;> rfl
  have freshReg : (requested.base.fresh .int).1 = .vreg requested.base.nextVreg .int := rfl
  rw [freshReg] at root
  have actual := acquire_record_binding run events records R.rootInstalled results resultReg recorded emitted root
  have final := acquire_selected_final_binding run scope dominated events records R.rootInstalled R.rootSource results resultReg
    recorded emitted selectedId
  obtain ⟨actualDest,lower,actualResults,finalAlias,finalNum⟩ := final
  have destEq : actualDest = requested.base.nextVreg := by
    have equal := actualResults.symm.trans actual.2.1
    simpa only [List.cons.injEq,List.nil.injEq,and_true,Reg.vreg.injEq] using equal
  subst actualDest
  refine ⟨R,pointerReg,requested.base.nextVreg,resultId,key,register,results,resultReg,fresh,?_,actual.2.1,finalAlias,finalNum⟩
  rw [actual.2.2,state]
  simp only [LState.emit,LState.fresh,requestedBase,scanState]
  split <;> rfl

end Backend.Stock.Proof.Acquire810

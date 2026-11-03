import FV.Backend.Proof.StockAcquireMatchArgumentFields

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual retained selection emits the original atomic type and flags, with no external code certificate. -/
theorem stock_lower_acquire_selected_emission {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (middle requested : State) (address : Reg)
      (next bound : State) (copies : List MInst),
      Stock.externCtor event.ctx T.sink_inst [.inst R.producer] (scanState record.input record.inst) =
        .ok (.op .unit,middle) ∧
      Stock.externCtor event.ctx T.put_in_reg [.value R.pointer] middle = .ok (.reg address,requested) ∧
      event.ctx.valueReg? R.pointer = some address ∧ requested = middle.mark R.pointer ∧
      next = {requested with base := (requested.base.fresh .int).2.emit
        (.loadAcquire (CTy.ofClif R.ty) (requested.base.fresh .int).1 address R.flags)} ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some (.regsVec [[(requested.base.fresh .int).1]]),next,step.rules.toArray) ∧
      bindResults event.ctx (event.ctx.insts[record.inst]!.results.zip [[(requested.base.fresh .int).1]]) next =
        .ok (bound,copies) ∧
      record.output.state = bound ∧ record.output.emitted = bound.base.emitted ++ copies := by
  obtain ⟨R⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events records recorded emitted selectedId
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by rw [← receipt.rules];exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 := ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := receipt.selected.rhsRun
  rw [chosen] at rhs
  have mapped := (stock_lower_record_context run scope events).1
  obtain ⟨actualProducer,source,stateEq,traceEq,producerValue⟩ :=
    acquire_root_match_original_value mapped R.rootInstalled R.rootSource matched
  have actualDefined := (source_effect_eligible source (by
    obtain ⟨value,producer,sunk,info,ty,flags,pointer,defined,once,arity,positive,color,
      sink,state,installed,original,integer,little,binding,sameState,sameTrace⟩ :=
      acquire_rule_pending_source mapped (n := 999979) matched rhs
    have equal := V.inst.inj (Option.some.inj (Option.some.inj (producerValue.symm.trans binding)))
    simpa only [equal] using positive)).1
  have producerEq : actualProducer = R.producer := Option.some.inj (actualDefined.symm.trans R.defined)
  subst actualProducer
  rw [stateEq,traceEq] at rhs
  obtain ⟨typeV,flagsV,typeValue,flagValue⟩ := AcquireHelpers.acquire_rhs_inputs (n := 999979) rhs
  obtain ⟨addressValue,requested,sinkTrace,instruction,called,decoded,output,state,fresh⟩ :=
    AcquireHelpers.acquire_rhs_output (n := 999899) typeValue flagValue producerValue rhs
  obtain ⟨actual,rest,found,shape⟩ := AcquireHelpers.sink_atomic_call_data (by omega : 10 ≤ 999992) called
  have infoEq := Option.some.inj (found.symm.trans R.installed)
  subst actual
  have atomic := mapped_atomic_original_fields mapped R.installed R.source R.integer R.little shape
  obtain ⟨env,args,iflets⟩ := matchRule_some_inv (m := m+4) matched
  have originalData := acquire_original_extension_data mapped R.rootInstalled R.rootSource
  have held := acquire_root_args_value_data R.rootInstalled originalData args
  obtain ⟨actualRoot,rootFound,rootData⟩ := acquire_root_args_original_operand_data args held
  have rootEq := Option.some.inj (rootFound.symm.trans R.rootInstalled)
  subst actualRoot
  obtain ⟨tys,types,resultTypes,length⟩ := mapped.resTys record.inst R.rootInfo _ R.rootInstalled R.rootSource
  have tysEq : tys = [R.target] := by simpa only [Clif.Inst.resultTypes,Option.some.injEq] using types.symm
  have rootType : R.rootInfo.resTys.head?.getD .invalid = CTy.ofClif R.target := by rw [resultTypes,tysEq];rfl
  have fits : (CTy.ofClif R.target).bits ≤ 64 := by
    have bits : (CTy.ofClif R.target).bits = R.target.width := by cases R.target <;> rfl
    rw [bits]
    exact R.fits
  have valueType := stock_lower_acquire_source_type run scope dominated events R.defined R.installed R.source
  have fields := acquire_root_match_argument_fields R.little R.rootInstalled rootData rootType fits valueType
    R.defined R.installed atomic matched
  obtain ⟨actualTy,actualFlags,actualPointer,middle,address,sourceEq,integer,little,sink,request,safe,register,returned,marked⟩ :=
    sink_atomic_original_request mapped R.installed R.source (fuel := 999992) (by omega) called
  have sourceFields := Clif.Inst.atomicLoad.inj sourceEq
  rcases sourceFields with ⟨rfl,rfl,rfl⟩
  have forward := AcquireHelpers.acquire_rhs_forward data_program event.ctx (cfg := {}) rfl R.installed atomic sink request
    fields.1 fields.2 producerValue #[] 999919
  have same := Except.ok.inj (rhs.symm.trans forward)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have nextEq := congrArg (fun x => x.2.1) same
  refine ⟨R,middle,requested,address,receipt.next,_,receipt.copies,sink,request,register,marked,nextEq,?_,?_,receipt.state,receipt.code⟩
  · rw [← outEq]
    have root := receipt.rootRun
    have rules : receipt.fired = step.rules.toArray := by rw [← receipt.rules];simp
    simpa only [rules] using root
  · simpa only [outEq] using receipt.binding

end Backend.Stock.Proof.Acquire810

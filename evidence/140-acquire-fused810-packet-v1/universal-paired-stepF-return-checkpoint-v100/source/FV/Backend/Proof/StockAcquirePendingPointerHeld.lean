import FV.Backend.Proof.StockAcquirePendingRequestGuard

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual source/mark provenance discharges the selected pointer's machine binding from the pending invariant. -/
theorem stock_lower_acquire_pending_pointer_held {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier record.output.state) (retired : RetiredUndemanded frontier record.output.state)
    {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld frontier.history
      (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) event.block R.consumerIndex)
      frame regs) : ValueHeld event.ctx frame regs R.pointer := by
  have pending := frontier_pending_values held retired
  have pendingRetained : ∀ captured ∈ frontier.pending,captured.record ∈ event.output.records := by
    intro captured member
    apply retained captured
    rw [frontier.split]
    exact List.mem_append_right _ member
  have notSuspended := stock_lower_allowed_not_suspended run scope dominated events pendingRetained marked
    (stock_lower_acquire_pointer_demand_allowed run scope dominated events records recorded emitted selectedId R)
  obtain ⟨producer,info,ty,flags,pointer,address,defined,installed,source,integer,little,register,demanded⟩ :=
    stock_lower_acquire_selected_original_pointer_demanded run scope events records R.rootInstalled R.rootSource
      recorded emitted selectedId
  have producerEq := Option.some.inj (defined.symm.trans R.defined)
  subst producer
  have infoEq := Option.some.inj (installed.symm.trans R.installed)
  subst info
  have pointerEq := (Clif.Inst.atomicLoad.inj (Option.some.inj (source.symm.trans R.source))).2.2
  rw [pointerEq] at demanded
  obtain ⟨otherProducer,otherInfo,otherTy,otherFlags,otherPointer,otherDefined,otherInstalled,otherSource,
    otherInteger,otherLittle,available⟩ := stock_lower_acquire_selected_pointer_available run scope dominated events records
      R.blockAt R.consumerAt R.current R.rootInstalled R.rootSource recorded emitted selectedId
  have otherProducerEq := Option.some.inj (otherDefined.symm.trans R.defined)
  subst otherProducer
  have otherInfoEq := Option.some.inj (otherInstalled.symm.trans R.installed)
  subst otherInfo
  have otherPointerEq := (Clif.Inst.atomicLoad.inj (Option.some.inj (otherSource.symm.trans R.source))).2.2
  rw [otherPointerEq] at available
  exact pending R.pointer ⟨demanded,available⟩ notSuspended

end Backend.Stock.Proof.Acquire810

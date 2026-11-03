import FV.Backend.Proof.StockAcquirePartialPrefixValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original dominance makes the selected pointer available from its producer onward, before any later fault. -/
theorem stock_lower_acquire_pointer_available_at_prefix {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {cut : Nat} (order : R.producerIndex ≤ cut) :
    R.pointer ∈ availOf f (availIn f result.ctx) event.block cut := by
  obtain ⟨producerRecord,retained,position,marked⟩ :=
    stock_lower_acquire_actual_producer_record run scope events records recorded emitted selectedId R
  have installed := R.installed
  rw [← position] at installed
  have before := stock_lower_record_args_available run scope dominated events R.blockAt R.producerAt
    (position.trans R.position) installed R.source R.pointer (by simp [Driver.instArgs])
  exact availOf_index_mono order R.pointer before

/-- Actual pending values supply the pointer at a finite source prefix; the consumer need not execute. -/
theorem stock_lower_acquire_pending_pointer_at_prefix {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {cut : Nat} (order : R.producerIndex ≤ cut)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier record.output.state) (retired : RetiredUndemanded frontier record.output.state)
    {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld frontier.history
      (fun value => Demanded record.output.state value ∧ value ∈ availOf f (availIn f result.ctx) event.block cut)
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
  exact pending R.pointer ⟨demanded,stock_lower_acquire_pointer_available_at_prefix run scope dominated
    events records recorded emitted selectedId R order⟩ notSuspended

end Backend.Stock.Proof.Acquire810

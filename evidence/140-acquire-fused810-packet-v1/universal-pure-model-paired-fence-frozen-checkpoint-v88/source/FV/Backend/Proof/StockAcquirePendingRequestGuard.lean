import FV.Backend.Proof.StockAcquireCaptureDefinitions

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Successful actual register demand derives its existing unsunk-definition guard. -/
theorem put_in_reg_demand_allowed {ctx : Ctx} {before after : State} {value : Nat} {reg : Reg}
    (requested : Stock.externCtor ctx T.put_in_reg [.value value] before = .ok (.reg reg,after)) :
    DemandAllowed ctx before value := by
  intro producer defined
  cases marked : before.sunk[producer]! with
  | false => rfl
  | true =>
    simp only [Stock.externCtor,T.put_in_reg,defined,marked,ite_true] at requested
    cases requested

/-- Actual endpoint receipts identify the same original atomic pointer. -/
theorem source_endpoint_pointer_unique {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (first second : SourceEndpointReceipt f event record) : first.pointer = second.pointer := by
  have producerEq := source_endpoint_producer_unique first second
  have firstInstalled := first.installed
  rw [producerEq] at firstInstalled
  have infoEq := Option.some.inj (firstInstalled.symm.trans second.installed)
  have sourceEq := first.source
  rw [infoEq,second.source] at sourceEq
  exact ((Clif.Inst.atomicLoad.inj (Option.some.inj sourceEq)).2.2).symm

/-- The original selected pointer remains demand-allowed at the actual record's machine entry. -/
theorem stock_lower_acquire_pointer_demand_allowed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    DemandAllowed event.ctx record.output.state R.pointer := by
  obtain ⟨actual,middle,requested,address,next,bound,copies,sink,request,register,marked,state,root,binding,final,code⟩ :=
    stock_lower_acquire_selected_emission run scope dominated events records recorded emitted selectedId
  have safe := put_in_reg_demand_allowed request
  have producerEq := source_endpoint_producer_unique actual R
  have pointerEq := source_endpoint_pointer_unique actual R
  have sinkState := (sink_accepted sink).2.2.2.2
  have actualMarks : record.output.state.sunk = middle.sunk := by
    rw [stock_lower_acquire_sunk_delta run scope events records recorded emitted selectedId R,sinkState]
    simp only [scanState_sunk,producerEq]
  intro producer defined
  rw [actualMarks]
  exact safe producer (by rwa [pointerEq])

/-- Actual requests cannot refer to the results of any synchronized outstanding captured producer. -/
theorem stock_lower_allowed_not_suspended {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    {state : State} {value : Nat}
    (retained : ∀ captured ∈ frontier.pending,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier state) (allowed : DemandAllowed event.ctx state value) :
    ¬SuspendedReadResult frontier.pending value := by
  rintro ⟨captured,member,resultMember⟩
  have defined := stock_lower_sunk_snapshot_definitions run scope dominated events captured (retained captured member) value resultMember
  have safe := allowed captured.record.inst defined
  have sunk := marked captured member
  rw [safe] at sunk
  cases sunk

end Backend.Stock.Proof.Acquire810

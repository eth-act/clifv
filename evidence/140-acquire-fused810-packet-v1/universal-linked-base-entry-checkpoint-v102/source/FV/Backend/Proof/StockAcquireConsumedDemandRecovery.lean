import FV.Backend.Proof.StockAcquireSunkPendingTransfer

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual endpoint receipts for one consumer identify the same original producer. -/
theorem source_endpoint_producer_unique {f : Clif.Function} {event : BlockScanEvent} {record : ScanRecord}
    (first second : SourceEndpointReceipt f event record) : first.producer = second.producer := by
  have infoEq := Option.some.inj (first.rootInstalled.symm.trans second.rootInstalled)
  have sourceEq := first.rootSource
  rw [infoEq,second.rootSource] at sourceEq
  simp only [Option.some.injEq,Clif.Inst.extend.injEq] at sourceEq
  have valueEq := sourceEq.2.2
  have other : event.ctx.defInst? first.value = some second.producer := by
    rw [← valueEq]
    exact second.defined
  exact Option.some.inj (first.defined.symm.trans other)

/-- The actual selected sink proves that its captured producer results are not demanded after consumption. -/
theorem stock_lower_acquire_consumed_results_undemanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    ∀ value ∈ event.ctx.insts[R.producer]!.results,record.input.demand[value]! = 0 := by
  obtain ⟨actual,middle,requested,address,next,bound,copies,sink,request,register,marked,state,root,binding,final,code⟩ :=
    stock_lower_acquire_selected_emission run scope dominated events records recorded emitted selectedId
  have producerEq := source_endpoint_producer_unique actual R
  have zeros := (sink_accepted sink).2.2.1
  simpa only [producerEq,scanState_demands] using zeros

/-- Removing an actually undemanded capture preserves every other required source binding. -/
theorem pending_values_discharge {ctx : Ctx} {env : Clif.Env} {program : Clif.Program}
    {remaining : List (SunkReadSnapshot ctx env program)} {captured : SunkReadSnapshot ctx env program}
    {demand : Nat → Prop} {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld (remaining++[captured]) demand frame regs)
    (undemanded : ∀ value ∈ ctx.insts[captured.record.inst]!.results,¬demand value) :
    PendingValuesHeld remaining demand frame regs := by
  intro value required notRemaining
  apply held value required
  rintro ⟨other,member,result⟩
  rcases List.mem_append.mp member with old | last
  · exact notRemaining ⟨other,old,result⟩
  · have same := List.mem_singleton.mp last
    subst other
    exact undemanded value result required

/-- A consumer discharges only its actual selected producer; the remaining frontier stays general. -/
theorem stock_lower_acquire_discharge_capture {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record)
    {env : Clif.Env} {program : Clif.Program} {captured : SunkReadSnapshot event.ctx env program}
    (producer : captured.record.inst = R.producer) {remaining : List (SunkReadSnapshot event.ctx env program)}
    {available : Nat → Prop} {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld (remaining++[captured]) (fun value => Demanded record.input value ∧ available value) frame regs) :
    PendingValuesHeld remaining (fun value => Demanded record.input value ∧ available value) frame regs := by
  apply pending_values_discharge held
  intro value member required
  have zero := stock_lower_acquire_consumed_results_undemanded run scope dominated events records recorded emitted selectedId R
    value (by simpa only [producer] using member)
  exact required.1 zero

end Backend.Stock.Proof.Acquire810

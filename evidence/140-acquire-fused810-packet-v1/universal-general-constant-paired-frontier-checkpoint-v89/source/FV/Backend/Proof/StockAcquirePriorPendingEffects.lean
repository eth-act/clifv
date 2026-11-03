import FV.Backend.Proof.StockAcquireCrossedEffectRecord

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual complete groups place every other deferred effect on its original side of selected810's producer.
Groups use backward scan order; their complete reversal supplies forward chunk order. Empty pure groups remain included. -/
theorem stock_lower_acquire_pending_effect_partition {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ (R : SourceEndpointReceipt f event record) (groups later earlier : List (List Nat)),
      ExecutedRecordFrontiers f event.ctx event.output.records groups ∧
      groups = later++[R.producer]::earlier ∧
      (∀ producer ∈ earlier.flatten,producer < R.producer) ∧
      (∀ producer ∈ later.flatten,R.producer < producer) := by
  obtain ⟨R⟩ := stock_lower_acquire_source_endpoint_receipt run scope dominated events records recorded emitted selectedId
  obtain ⟨groups,frontiers,marks,ordered⟩ := stock_lower_event_executed_source_order run scope events
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  obtain ⟨later,pending,earlier,parts,frontier,inputMarks⟩ :=
    ScansSpec.executed_record_group_prefix actual frontiers records
  have singleton := executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier
  rw [singleton] at parts
  rw [parts,List.flatten_append,List.flatten_cons] at ordered
  change List.Pairwise (fun first second => second < first) (later.flatten++R.producer::earlier.flatten) at ordered
  refine ⟨R,groups,later,earlier,frontiers,parts,?_,?_⟩
  · intro producer member
    exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 producer member
  · intro producer member
    exact (List.pairwise_append.mp ordered).2.2 producer member R.producer (List.mem_cons_self ..)

end Backend.Stock.Proof.Acquire810

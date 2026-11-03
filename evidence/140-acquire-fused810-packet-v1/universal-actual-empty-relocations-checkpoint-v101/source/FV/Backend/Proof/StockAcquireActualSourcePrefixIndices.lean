import FV.Backend.Proof.StockAcquireActualPendingHead

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual forward record list retains precisely the original contiguous source range. -/
theorem stock_lower_event_forward_source_indices {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ block,f.blocks[event.block]? = some block ∧
      event.output.records.reverse.map (·.inst) = List.range' (blockStart f event.block) (block.body.length+1) := by
  obtain ⟨block,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have actual := runScans_spec (stock_lower_event_scan_run run events)
  refine ⟨block,split.block,?_⟩
  rw [List.map_reverse,actual.order,split.indices,List.reverse_cons]
  simp only [sourceBodyIndices,List.reverse_reverse]
  rw [split.termIndex,List.range'_1_concat,List.range'_eq_map_range]

/-- The selected consumer's source index derives its exact retained forward prefix. -/
theorem stock_lower_acquire_source_prefix_indices {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    (R : SourceEndpointReceipt f event record) :
    (event.output.records.reverse.take R.consumerIndex).map (·.inst) =
      List.range' (blockStart f event.block) R.consumerIndex := by
  obtain ⟨block,blockAt,indices⟩ := stock_lower_event_forward_source_indices run scope events
  have blockEq := Option.some.inj (blockAt.symm.trans R.blockAt)
  subst block
  have inside := (List.getElem?_eq_some_iff.mp R.consumerAt).1
  rw [List.map_take,indices]
  exact List.take_range'_of_length_ge (by omega)

/-- Actual finite source execution constructs the exact retained read history without a prefix-index certificate. -/
theorem stock_lower_acquire_source_steps_captures {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    (R : SourceEndpointReceipt f event record) {env : Clif.Env} {program : Clif.Program}
    {before after : Clif.Frame × Clif.Mem}
    (executed : SourceSteps (SourceInstResult env program event.ctx)
      (List.range' (blockStart f event.block) R.consumerIndex) before after) :
    ∃ captures,SourceReadCaptures event.ctx env program (event.output.records.reverse.take R.consumerIndex) before after captures ∧
      ∀ captured ∈ captures,captured.record ∈ event.output.records := by
  have actualSteps : SourceSteps (SourceInstResult env program event.ctx)
      ((event.output.records.reverse.take R.consumerIndex).map (·.inst)) before after := by
    rw [stock_lower_acquire_source_prefix_indices run scope events R]
    exact executed
  exact stock_lower_actual_prefix_read_captures run scope events R.consumerIndex actualSteps

end Backend.Stock.Proof.Acquire810

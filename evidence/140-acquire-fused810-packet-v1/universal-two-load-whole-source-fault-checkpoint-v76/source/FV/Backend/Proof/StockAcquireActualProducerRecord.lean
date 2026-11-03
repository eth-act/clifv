import FV.Backend.Proof.StockAcquireMarkPropagation

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual selected root execution marks its exact original producer inside the real mark array. -/
theorem stock_lower_acquire_output_producer_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    record.output.state.sunk[R.producer]! = true := by
  obtain ⟨pending,frontier⟩ := stock_lower_record_executed_frontier run events records
  have singleton := executed_frontier_acquire_singleton run scope events records recorded emitted selectedId R frontier
  have trace := (frontier.2 step recorded emitted).forget
  have member : R.producer ∈ pending := by rw [singleton];exact List.mem_singleton_self _
  have positive := trace.member_positive member
  have inside : R.producer < (scanState record.input record.inst).entryColor.size := by
    apply Classical.byContradiction
    intro outside
    have absent := Array.getElem?_eq_none (Nat.le_of_not_lt outside)
    simp only [getElem!_def,absent] at positive
    exact positive rfl
  have size : (scanState record.input record.inst).sunk.size = (scanState record.input record.inst).entryColor.size := by
    rw [scanState_sunk,scanState_entry_colors]
    exact stock_lower_record_sunk_color_extent run events records
  exact trace.member_marked (by rwa [size]) member

/-- The actual original producer record exists and inherits its consumer's real sink mark. -/
theorem stock_lower_acquire_actual_producer_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) (R : SourceEndpointReceipt f event record) :
    ∃ producerRecord ∈ event.output.records,producerRecord.inst = R.producer ∧
      producerRecord.input.sunk[producerRecord.inst]! = true := by
  obtain ⟨block,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have blockEq := Option.some.inj (split.block.symm.trans R.blockAt)
  subst block
  have bound := (List.getElem?_eq_some_iff.mp R.producerAt).1
  have sourceMember : R.producer ∈ sourceBodyIndices f event.block R.block := by
    simp only [sourceBodyIndices,List.mem_reverse,List.mem_map]
    exact ⟨R.producerIndex,List.mem_range.mpr bound,R.position.symm⟩
  rw [← split.scanned.order] at sourceMember
  obtain ⟨producerRecord,member,position⟩ := List.mem_map.mp sourceMember
  have retained := split.retained producerRecord member
  have marked := stock_lower_acquire_output_producer_marked run scope events records recorded emitted selectedId R
  have order : producerRecord.inst < record.inst := by
    have before := R.before
    rw [position,R.position,R.current]
    omega
  have producerMark := stock_lower_record_mark_propagates run events records retained order marked
  refine ⟨producerRecord,retained,position,?_⟩
  simpa only [position] using producerMark

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockAcquireActualSourceView
import FV.Backend.Proof.StockAcquireCoreMarkFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- Exact actual read folds retain inherited marks and classify all newly marked original slots. -/
theorem ReadMarked.of_read_fold {original current : Ctx} {before after : State} {pending : List Nat}
    (view : SourceSlotsPreserved original current) (prior : ReadMarked original before)
    (folded : after.sunk = pending.foldl (fun bits producer => bits.set! producer true) before.sunk)
    (frames : ∀ producer ∈ pending,SourceReadFrame current producer) : ReadMarked original after := by
  intro producer marked
  rw [folded] at marked
  rcases sunk_fold_marked before.sunk pending producer marked with inherited | member
  · exact prior producer inherited
  · exact (frames producer member).of_source_view view

/-- Actual retained scans preserve inherited original read marks at every recorded boundary. -/
theorem stock_lower_scan_read_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) (prior : ReadMarked result.ctx event.input) :
    ReadMarked result.ctx event.output.state ∧
      ∀ record ∈ event.output.records,ReadMarked result.ctx record.input ∧ ReadMarked result.ctx record.output.state := by
  have view := stock_lower_event_original_slots run scope events
  obtain ⟨groups,frontiers,reversed,exactSunk,frames,assembly⟩ := stock_lower_event_read_frontiers run events
  have sourceFrames : ∀ producer ∈ groups.flatten,SourceReadFrame event.ctx producer := by
    intro producer member
    obtain ⟨group,groupMember,producerMember⟩ := List.mem_flatten.mp member
    exact frames producer (List.mem_flatten.mpr ⟨group,List.mem_reverse.mpr groupMember,producerMember⟩)
  refine ⟨prior.of_read_fold view exactSunk sourceFrames,?_⟩
  intro record records
  obtain ⟨pending,prefixSunk,prefixFrames,provenance⟩ := stock_lower_record_marked_read_provenance run events records
  have recordInput : ReadMarked result.ctx record.input := prior.of_read_fold view prefixSunk prefixFrames
  obtain ⟨nextPending,nextFrontier,nextFrames⟩ := stock_lower_record_read_frontier run events records
  exact ⟨recordInput,recordInput.of_read_fold view nextFrontier.1 nextFrames⟩

/-- Real branch/outgoing frames and actual scan reads preserve original marks through a complete block core. -/
theorem stock_lower_actual_core_read_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {order : Order} {block : Clif.Block}
    {bi start stop : Nat} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (coreRun : lowerBlockCore result.ctx order f block bi start stop data targets input = .ok output)
    (events : output.scan ∈ result.blockScans.toList) (prior : ReadMarked result.ctx input) :
    ReadMarked result.ctx output.state ∧ ReadMarked result.ctx output.scan.input := by
  have fields := blockCore_scan_input_sunk coreRun
  have start : ReadMarked result.ctx output.scan.input := prior.of_sunk_eq fields.1
  have scanned := (stock_lower_scan_read_marked run scope events start).1
  exact ⟨scanned.of_sunk_eq fields.2,start⟩

end Backend.Stock.Proof.Acquire810

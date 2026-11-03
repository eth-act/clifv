import FV.Backend.Proof.StockAcquireDriverReadMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] lowerNode

/-- Actual full Stock execution derives source read frames for all final and inherited entry marks. -/
theorem stock_lower_all_read_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ReadMarked result.ctx result.final ∧
      ∀ event ∈ result.blockScans.toList,ReadMarked result.ctx event.input := by
  have actualRun := run
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  rename_i _ built hbuild _ order horder _ driver hdriver
  have initial : DriverReadMarked built.1 {
      state := built.2.2
      blocks := Array.replicate order.nodes.size default
      edgeArgs := Array.replicate order.nodes.size #[]
      schedule := #[],scans := #[],blockScans := #[],rules := #[] } := by
    refine ⟨buildCtx_read_marked hbuild,?_⟩
    simp
  exact stock_lower_actual_nodes_read_marked actualRun scope hdriver (fun event member => member) initial

/-- Every marked source before an actual retained record derives its read frame, including inherited entry marks. -/
theorem stock_lower_record_marked_source_read {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    (producer : Nat) (marked : record.input.sunk[producer]! = true) : SourceReadFrame event.ctx producer := by
  have entry := (stock_lower_all_read_marked run scope).2 event events
  have recordsMarked := (stock_lower_scan_read_marked run scope events entry).2 record records
  have read := recordsMarked.1 producer marked
  have view : SourceSlotsPreserved event.ctx result.ctx := by
    intro slot info inst installed source
    exact (stock_lower_record_context run scope events).2.2 slot info inst installed source
  exact read.of_source_view view

end Backend.Stock.Proof.Acquire810

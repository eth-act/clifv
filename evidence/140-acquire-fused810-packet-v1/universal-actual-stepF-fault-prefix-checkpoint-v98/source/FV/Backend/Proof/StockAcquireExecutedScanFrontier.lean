import FV.Backend.Proof.StockAcquireExecutedRecordFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A complete internal scan frontier retains every actual emitted interpreter obligation. -/
inductive ExecutedRecordFrontiers (f : Clif.Function) (ctx : Ctx) : List ScanRecord → List (List Nat) → Prop where
  | nil : ExecutedRecordFrontiers f ctx [] []
  | cons {record : ScanRecord} {pending : List Nat} {records : List ScanRecord} {groups : List (List Nat)}
      (head : ExecutedRecordFrontier f ctx record pending) (tail : ExecutedRecordFrontiers f ctx records groups) :
      ExecutedRecordFrontiers f ctx (record::records) (pending::groups)

/-- The stronger complete frontier preserves the entire old frontier interface. -/
theorem ExecutedRecordFrontiers.forget {f : Clif.Function} {ctx : Ctx}
    {records : List ScanRecord} {groups : List (List Nat)} (frontiers : ExecutedRecordFrontiers f ctx records groups) :
    RecordFrontiers f ctx records groups := by
  induction frontiers with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.1 ih

/-- Every complete real scan derives its stronger groups from its actual callbacks. -/
theorem ScansSpec.executed_frontiers {f : Clif.Function} {ctx : Ctx}
    {exec : Nat → State → Except String Scan} {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec exec indices before output)
    (localFrontier : ∀ record ∈ output.records,∃ pending,ExecutedRecordFrontier f ctx record pending) :
    ∃ groups,ExecutedRecordFrontiers f ctx output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) before.sunk := by
  revert localFrontier
  induction spec with
  | nil input => intro localFrontier;exact ⟨[],.nil,rfl⟩
  | @cons inst indices before scan tail head rest ih =>
    intro localFrontier
    obtain ⟨pending,frontier⟩ := localFrontier _ (List.mem_cons_self ..)
    obtain ⟨groups,frontiers,exactSunk⟩ := ih (fun record member => localFrontier record (List.mem_cons_of_mem _ member))
    refine ⟨pending::groups,.cons frontier frontiers,?_⟩
    rw [List.flatten_cons,List.foldl_append,← frontier.1.1]
    exact exactSunk

/-- Actual Stock lowering supplies all stronger groups, including pure emitted empty groups. -/
theorem stock_lower_event_executed_frontiers {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ groups,ExecutedRecordFrontiers f event.ctx event.output.records groups ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk :=
  ScansSpec.executed_frontiers (runScans_spec (stock_lower_event_scan_run run events))
    (fun record member => stock_lower_record_executed_frontier run events member)

/-- The complete stronger queue derives strict source order without a caller trace certificate. -/
theorem stock_lower_event_executed_source_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ groups,ExecutedRecordFrontiers f event.ctx event.output.records groups ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      groups.flatten.Pairwise (fun first second => second < first) := by
  obtain ⟨groups,frontiers,exactSunk⟩ := stock_lower_event_executed_frontiers run events
  have ordered := stock_lower_event_record_pending_colors_order run scope events
  exact ⟨groups,frontiers,exactSunk,frontiers.forget.flatten_source_order run events (fun record member => member) ordered⟩

end Backend.Stock.Proof.Acquire810

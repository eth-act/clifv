import FV.Backend.Proof.StockAcquireScanFrontiers

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Frontier composition keeps every record associated with its own pending group. -/
theorem RecordFrontiers.append {f : Clif.Function} {ctx : Ctx}
    {left right : List ScanRecord} {leftGroups rightGroups : List (List Nat)}
    (first : RecordFrontiers f ctx left leftGroups) (second : RecordFrontiers f ctx right rightGroups) :
    RecordFrontiers f ctx (left++right) (leftGroups++rightGroups) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head (ih second)

/-- Forward assembly reverses complete groups together with their retained records. -/
theorem RecordFrontiers.reverse {f : Clif.Function} {ctx : Ctx}
    {records : List ScanRecord} {groups : List (List Nat)}
    (frontiers : RecordFrontiers f ctx records groups) :
    RecordFrontiers f ctx records.reverse groups.reverse := by
  induction frontiers with
  | nil => exact .nil
  | cons head tail ih =>
    simpa only [List.reverse_cons] using ih.append (.cons head .nil)

/-- Every member of the complete derived queue belongs to the original source effect list. -/
theorem RecordFrontiers.source_members {f : Clif.Function} {ctx : Ctx}
    {records : List ScanRecord} {groups : List (List Nat)}
    (frontiers : RecordFrontiers f ctx records groups) :
    ∀ producer ∈ groups.flatten,OriginalPendingSource f producer := by
  induction frontiers with
  | nil => simp
  | cons head tail ih =>
    intro producer member
    rcases List.mem_append.mp member with member | member
    · exact head.2.1 producer member
    · exact ih producer member

/-- Actual Stock assembly derives forward record/frontier association without a caller schedule. -/
theorem stock_lower_event_forward_frontiers {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ groups : List (List Nat),
      RecordFrontiers f event.ctx event.output.records groups ∧
      RecordFrontiers f event.ctx event.output.records.reverse groups.reverse ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      (∀ producer ∈ groups.reverse.flatten,OriginalPendingSource f producer) ∧
      event.output.code.toList = event.output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  exact ⟨groups,frontiers,frontiers.reverse,exactSunk,frontiers.reverse.source_members,assembly⟩

end Backend.Stock.Proof.Acquire810

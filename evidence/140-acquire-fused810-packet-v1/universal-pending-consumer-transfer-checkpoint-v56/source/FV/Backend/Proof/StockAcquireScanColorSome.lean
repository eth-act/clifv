import FV.Backend.Proof.StockAcquireRecordColorOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful real sink traces cannot discard an existing execution color. -/
theorem PendingSinks.color_some {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {color : Nat} (initial : before.color = some color) :
    ∃ final,after.color = some final ∧ final ≤ color := by
  induction trace generalizing color with
  | nil => exact ⟨color,initial,Nat.le_refl _⟩
  | @sink before middle after producer rest actual tail ih =>
    have accepted := sink_accepted actual
    have middleColor : middle.color = some before.entryColor[producer]! := by rw [accepted.2.2.2.2]
    obtain ⟨final,finished,bound⟩ := ih middleColor
    have equal := Option.some.inj (initial.symm.trans accepted.2.1)
    exact ⟨final,finished,by omega⟩
  | frame entries unchanged tail ih => exact ih (unchanged.trans initial)

/-- Every actual record preserves the existence of its incoming execution color. -/
theorem stock_lower_record_color_some {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {color : Nat} (initial : record.input.color = some color) :
    ∃ final,record.output.state.color = some final := by
  have scanned : ∃ start,(scanState record.input record.inst).color = some start := by
    by_cases zero : record.input.entryColor[record.inst]! = 0
    · exact ⟨color,(scanState_color_zero record.input record.inst zero).trans initial⟩
    · exact ⟨_,scanState_color_positive record.input record.inst zero⟩
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,trace,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
    obtain ⟨start,started⟩ := scanned
    obtain ⟨final,finished,bound⟩ := trace.forget.forget.color_some started
    exact ⟨final,finished⟩
  · have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
    cases sunk : record.input.sunk[record.inst]! with
    | true =>
      have same := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input sunk))
      exact ⟨color,(congrArg (fun scan : Scan => scan.state.color) same).trans initial⟩
    | false =>
      obtain ⟨start,started⟩ := scanned
      have same := scan_no_emission_color sunk actual (fun step recorded emitted => emitting ⟨step,recorded,emitted⟩)
      exact ⟨start,same.trans started⟩

end Backend.Stock.Proof.Acquire810

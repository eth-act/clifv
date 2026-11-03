import FV.Backend.Proof.StockAcquireSourceColorPositive

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal block cap bounds the current color without imposing a moving-cut inequality. -/
def ColorUpperBound (cap : Nat) (state : State) : Prop :=
  ∀ color,state.color = some color → color ≤ cap

theorem ColorUpperBound.of_color_eq {cap : Nat} {before after : State}
    (bounded : ColorUpperBound cap before) (same : after.color = before.color) : ColorUpperBound cap after := by
  intro color actual
  exact bounded color (same.symm.trans actual)

theorem ColorUpperBound.at_color {cap color : Nat} {state : State}
    (actual : state.color = some color) (bound : color ≤ cap) : ColorUpperBound cap state := by
  intro target same
  have equal := Option.some.inj (actual.symm.trans same)
  omega

/-- Real deferred sinks only decrease the current color. -/
theorem PendingSinks.color_upper_bound {ctx : Ctx} {before after : State} {pending : List Nat} {cap : Nat}
    (trace : PendingSinks ctx before pending after) (bounded : ColorUpperBound cap before) :
    ColorUpperBound cap after := by
  intro final color
  have earlier := bounded _ (trace.color_distance color)
  omega

/-- Actual scan resets respect any cap that bounds their own original source slot. -/
theorem scanState_color_upper_bound {cap : Nat} (state : State) (inst : Nat)
    (bounded : ColorUpperBound cap state) (entry : state.entryColor[inst]! ≤ cap) :
    ColorUpperBound cap (scanState state inst) := by
  by_cases zero : state.entryColor[inst]! = 0
  · exact bounded.of_color_eq (scanState_color_zero state inst zero)
  · exact ColorUpperBound.at_color (scanState_color_positive state inst zero) entry

/-- Every actual record derives its output cap from real sink execution or its exact scan frame. -/
theorem stock_lower_record_color_upper_bound {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) {cap : Nat}
    (sunkBound : record.input.sunk[record.inst]! = true → ColorUpperBound cap record.input)
    (scanBound : ColorUpperBound cap (scanState record.input record.inst)) :
    ColorUpperBound cap record.output.state := by
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,marks,exactSunk,monotone⟩ := stock_lower_record_pending_marks run events records recorded emitted
    exact marks.forget.color_upper_bound scanBound
  · have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
    cases sunk : record.input.sunk[record.inst]! with
    | true =>
      have same := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input sunk))
      exact (sunkBound sunk).of_color_eq (congrArg (fun scan : Scan => scan.state.color) same)
    | false =>
      exact scanBound.of_color_eq (scan_no_emission_color sunk actual
        (fun step recorded emitted => emitting ⟨step,recorded,emitted⟩))

end Backend.Stock.Proof.Acquire810

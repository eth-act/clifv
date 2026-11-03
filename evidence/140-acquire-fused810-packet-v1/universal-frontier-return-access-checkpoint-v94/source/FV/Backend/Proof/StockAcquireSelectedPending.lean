import FV.Backend.Proof.StockAcquirePendingTrace
import FV.Backend.Proof.StockAcquireSelectedBinding
import FV.Backend.Proof.StockAcquireRuleSource

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual sinks and frontier-preserving helpers never erase an established color. -/
theorem PendingSinks.finalColor {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {initial : Nat} (color : before.color = some initial) :
    ∃ final,after.color = some final := by
  induction trace generalizing initial with
  | nil => exact ⟨initial,color⟩
  | @sink before middle after producer rest actual tail ih =>
    have middleColor : middle.color = some before.entryColor[producer]! := by
      rw [(sink_accepted actual).2.2.2.2]
    exact ih middleColor
  | frame entries unchanged tail ih => exact ih (unchanged.trans color)

/-- Every actual retained root810 derives its ordered pending frontier internally.
Multiple deferred effects remain admitted. No quiet-interval input premise is added. -/
theorem stock_lower_acquire_selected_pending {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ pending out next fired final,
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,fired) ∧
      PendingSinks event.ctx (scanState record.input record.inst) pending next ∧
      next.color = some final ∧
      (scanState record.input record.inst).color = some (final+pending.length) ∧
      pending.Pairwise (fun left right =>
        (scanState record.input record.inst).entryColor[right]! <
          (scanState record.input record.inst).entryColor[left]!) ∧ pending.Nodup := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have last : receipt.fired.getLast? = some 810 := by
    rw [← receipt.rules]
    exact selectedId
  have chosen := acquire_selected_rule receipt.selected last
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    rfl
  have fuel := receipt.selected.fuelBound
  rw [count] at fuel
  obtain ⟨m,fuelEq⟩ : ∃ m,receipt.selected.matchFuel = m+5 :=
    ⟨receipt.selected.matchFuel-5,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have rhs := receipt.selected.rhsRun
  rw [chosen] at rhs
  obtain ⟨value,producer,sunk,info,ty,flags,pointer,defined,once,arity,positive,color,
    sink,state,installed,original,integer,little⟩ :=
    acquire_rule_original_source (stock_lower_record_context run scope events).1
      (n := 999979) matched rhs
  obtain ⟨pending,actual⟩ := stock_runTerm_pending_execution receipt.rootRun
  obtain ⟨final,finalColor⟩ := actual.finalColor color
  exact ⟨pending,receipt.out,receipt.next,receipt.fired,final,receipt.rootRun,actual,finalColor,
    actual.color_distance finalColor,actual.ordered finalColor,actual.distinct finalColor⟩

end Backend.Stock.Proof.Acquire810

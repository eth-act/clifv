import FV.Backend.Proof.StockAcquireRulePendingSource
import FV.Backend.Proof.StockAcquireRhsPending

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The real retained record identifies its original atomic producer and exact deferred effect.
Prior pending loads remain admitted and no source interval must be quiet. -/
theorem stock_lower_acquire_selected_singleton {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    (selectedId : step.rules.getLast? = some 810) :
    ∃ value producer info ty flags pointer out next fired,
      event.ctx.defInst? value = some producer ∧
      (scanState record.input record.inst).uses[value]! = .once ∧
      event.ctx.insts[producer]? = some info ∧ info.clif = some (.atomicLoad ty flags pointer) ∧
      eTy ty = true ∧ flags.endianness ≠ some .big ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
        .ok (some out,next,fired) ∧
      PendingSinks event.ctx (scanState record.input record.inst) [producer] next ∧
      next.sunk = (scanState record.input record.inst).sunk.set! producer true ∧
      next.color = some (scanState record.input record.inst).entryColor[producer]! := by
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
    sink,state,installed,original,integer,little,binding,sameState,sameTrace⟩ :=
    acquire_rule_pending_source (stock_lower_record_context run scope events).1
      (n := 999979) matched rhs
  rw [sameState,sameTrace] at rhs
  obtain ⟨middle,sinkUnit,pending,sunkEq,colorEq⟩ := acquire_rhs_pending (n := 999899) binding rhs
  exact ⟨value,producer,info,ty,flags,pointer,receipt.out,receipt.next,receipt.fired,
    defined,once,installed,original,integer,little,receipt.rootRun,pending,sunkEq,colorEq⟩

end Backend.Stock.Proof.Acquire810

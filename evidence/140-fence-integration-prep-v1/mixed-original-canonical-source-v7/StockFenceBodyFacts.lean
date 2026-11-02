import FV.Backend.Proof.StockFenceWitness

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.lower

private def bodyFacts (event : BlockScanEvent) : Bool :=
  decide (event.block = 0) && decide (event.ctx.valueType? 100 = some (.int 64)) &&
    decide (event.ctx.defInst? 7 = none) && event.output.records.all fun record =>
      if record.inst < 7 then record.output.step.any fun step => decide (step.decision = .emitted) else true

private def allFacts : Option Bool :=
  (Stock.lower function).toOption.map fun result => result.blockScans.toList.all bodyFacts

private theorem allFacts_true : allFacts = some true := by native_decide

private theorem successful_exists {α : Type} (value : Except String α) (test : α → Bool)
    (success : value.toOption.map test = some true) :
    ∃ result,value = .ok result ∧ test result = true := by
  cases value with
  | error message => cases success
  | ok result => exact ⟨result,rfl,Option.some.inj success⟩

/-- Fixed source structure discharges retention and mapping facts for every actual event. -/
theorem mixed_actual_body_facts {result : Result} (run : Stock.lower function = .ok result)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    event.block = 0 ∧ event.ctx.valueType? 100 = some (.int 64) ∧ event.ctx.defInst? 7 = none ∧
      ∀ record ∈ event.output.records,record.inst < 7 →
        ∃ step,record.output.step = some step ∧ step.decision = .emitted := by
  have facts := allFacts_true
  unfold allFacts at facts
  obtain ⟨actual,lowered,checked⟩ := successful_exists (Stock.lower function) _ facts
  cases Except.ok.inj (lowered.symm.trans run)
  have row := List.all_eq_true.mp checked event events
  unfold bodyFacts at row
  obtain ⟨block,typed,parameter,each⟩ := (by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] using row :
      event.block = 0 ∧ event.ctx.valueType? 100 = some (.int 64) ∧ event.ctx.defInst? 7 = none ∧
        event.output.records.all (fun record => if record.inst < 7 then
          record.output.step.any fun step => decide (step.decision = .emitted) else true) = true)
  refine ⟨block,typed,parameter,?_⟩
  intro record member bound
  have got := List.all_eq_true.mp each record member
  simpa only [if_pos bound,Option.any_eq_true,decide_eq_true_eq] using got

end Backend.Stock.Proof.FenceFixture

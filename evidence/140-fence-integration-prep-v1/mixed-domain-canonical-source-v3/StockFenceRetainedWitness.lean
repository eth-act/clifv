import FV.Backend.Proof.StockFenceWitness

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.lower

private def retained : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    result.blockScans.toList.any fun event => decide (event.block = 0) &&
      (List.range 7).all fun i => event.output.records.any fun record =>
        decide (record.inst = i) && record.output.step.any fun step => decide (step.decision = .emitted)

private theorem retained_true : retained = some true := by native_decide

private theorem successful_exists {α : Type} (value : Except String α) (test : α → Bool)
    (success : value.toOption.map test = some true) :
    ∃ result,value = .ok result ∧ test result = true := by
  cases value with
  | error message => cases success
  | ok result => exact ⟨result,rfl,Option.some.inj success⟩

/-- Every statement of the unchanged complete mixed function has a retained emitted record. -/
theorem mixed_body_all_emitted :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      ∀ i < 7,∃ record,record ∈ event.output.records ∧ record.inst = i ∧
        ∃ step,record.output.step = some step ∧ step.decision = .emitted := by
  have checked := retained_true
  unfold retained at checked
  obtain ⟨result,run,checked⟩ := successful_exists (Stock.lower function) _ checked
  obtain ⟨event,events,block,all⟩ := (by
    simpa only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] using checked :
      ∃ event ∈ result.blockScans.toList,event.block = 0 ∧
        (List.range 7).all (fun i => event.output.records.any fun record =>
          decide (record.inst = i) && record.output.step.any fun step => decide (step.decision = .emitted)) = true)
  refine ⟨result,event,run,events,block,?_⟩
  intro i bounded
  have row := List.all_eq_true.mp all i (List.mem_range.mpr bounded)
  simpa only [List.any_eq_true,Option.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] using row

end Backend.Stock.Proof.FenceFixture

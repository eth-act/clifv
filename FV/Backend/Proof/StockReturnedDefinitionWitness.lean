import FV.Backend.Proof.StockReturnedDefinitionRetention
import FV.Backend.Proof.LowerDecide
import FV.E2E.StockDivFixtures

namespace Backend.Stock.Proof.ReturnedDefinitionWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-- Original nine-argument/stack-slot source, with a real pure suffix after the
returned division. The division is deliberately not the last source instruction. -/
def function : Clif.Function :=
  let old := E2E.StockDivNIWitness.function .defaultI64 .sdiv
  {old with name := "stock_returned_div_before_suffix",blocks := old.blocks.map fun b =>
    {b with body := b.body ++ [⟨[200],.iconst .i64 7⟩]}}
private def block : Clif.Block := function.blocks[0]!

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

private def checks : Bool :=
  dominatedB function && match Stock.lower function with
  | .error _ => false
  | .ok result => result.blockScans.toList.any fun event => event.block == 0

/-- Fixed actual lowering observation; no generic compiler theorem imports
this native fact. -/
theorem checks_true : checks = true := by native_decide

private theorem dominated : Dominated function := by
  have checked := checks_true
  simp only [checks,Bool.and_eq_true] at checked
  exact dominated_of checked.1

private theorem actual_run : ∃ result event,
    Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧
      function.blocks[event.block]? = some block := by
  have both := checks_true
  simp only [checks,Bool.and_eq_true] at both
  have checked := both.2
  cases run : Stock.lower function with
  | error message => rw [run] at checked; cases checked
  | ok result =>
    rw [run] at checked
    obtain ⟨event,member,zero⟩ := List.any_eq_true.mp checked
    have index : event.block = 0 := by simpa using zero
    exact ⟨result,event,rfl,member,by rw [index]; rfl⟩

/-- A successful whole-driver run with a non-final division inhabits the
positive actual return-demand theorem. Original arguments and slot remain. -/
theorem positive_demand_witness : ∃ result event term body step,
    LowerScope function ∧ Stock.lower function = .ok result ∧
    event ∈ result.blockScans.toList ∧ SourceBodySplit function event block term body ∧
    term ∈ event.output.records ∧ term.output.step = some step ∧ step.decision = .emitted ∧
    term.output.state.demand[100]! ≠ 0 ∧ block.body.length = 2 := by
  obtain ⟨result,event,run,member,found⟩ := actual_run
  obtain ⟨term,body,step,split,records,safe,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope member found (by rfl)
  have positive := stock_lower_return_positive_demand (x := 100) run scope member found
    (by rfl : block.term = .ret [100]) records split.termInst recorded emitted (by simp)
  exact ⟨result,event,term,body,step,scope,run,member,split,records,recorded,emitted,positive,rfl⟩

/-- The returned division at position zero is retained/emitted despite the
real later source statement. All original scope/SSA premises are inhabited. -/
theorem returned_div_emitted_witness : ∃ result event term record body step,
    LowerScope function ∧ Dominated function ∧ Stock.lower function = .ok result ∧
    event ∈ result.blockScans.toList ∧ SourceBodySplit function event block term body ∧
    record ∈ body.records ∧ record.inst = blockStart function event.block+0 ∧
    record.input.sunk[record.inst]! = false ∧ record ∈ event.output.records ∧
    record.output.step = some step ∧ step.decision = .emitted ∧ block.body.length = 2 := by
  obtain ⟨result,event,run,member,found⟩ := actual_run
  obtain ⟨term,record,body,step,split,records,current,safe,scanned,retained,recorded,emitted⟩ :=
    stock_lower_returned_div_emitted run scope dominated member found
      (by rfl : block.body[0]? = some ⟨[100],.div .sdiv .i64 1 8⟩)
      rfl rfl (by rfl : block.term = .ret [100])
  exact ⟨result,event,term,record,body,step,scope,dominated,run,member,split,
    records,current,safe,retained,recorded,emitted,rfl⟩

end Backend.Stock.Proof.ReturnedDefinitionWitness

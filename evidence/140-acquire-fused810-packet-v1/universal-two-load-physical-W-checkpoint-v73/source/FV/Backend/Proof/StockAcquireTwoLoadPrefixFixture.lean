import FV.Backend.Proof.StockAcquireFaultFrontier
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.Acquire810
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.lower

/-- The complete preserved two-load input keeps both original pointers, widths, flags, and consumers. -/
def function : Clif.Function := {
  name := "two_deferred_acquires"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.atomicLoad .i8 {} 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩,
    ⟨[101],.extend .uextend .i64 64⟩],term := .ret [100,101]}]}

/-- These observations name the actual complete traversal, including both sunk producers and both consumers. -/
def ActualSchedule (event : BlockScanEvent) : Prop :=
  let rs := event.output.records.reverse
  event.block = 0 ∧ rs.map (·.inst) = [0,1,2,3,4] ∧
  rs[0]!.output.state = event.output.state ∧
  rs[1]!.output.state = rs[0]!.input ∧ rs[2]!.output.state = rs[1]!.input ∧
  rs[3]!.output.state = rs[2]!.input ∧ rs[4]!.output.state = rs[3]!.input ∧
  rs[0]!.input.sunk[0]! = true ∧ rs[1]!.input.sunk[1]! = true ∧
  rs[2]!.output.step.map (·.rules.getLast?) = some (some 810) ∧
  rs[3]!.output.step.map (·.rules.getLast?) = some (some 810) ∧
  rs[2]!.output.step.map (·.decision) = some .emitted ∧
  rs[3]!.output.step.map (·.decision) = some .emitted

instance (event : BlockScanEvent) : Decidable (ActualSchedule event) := by
  unfold ActualSchedule
  infer_instance

private def observed : Option Bool := (Stock.lower function).toOption.map fun result =>
  decide (result.blockScans.size = 1) && lowerScopeB function && dominatedB function && sigAbiOk function.sig &&
    result.blockScans.toList.any (fun event => decide (ActualSchedule event))

-- witness: native_decide
private theorem observed_true : observed = some true := by native_decide

private theorem successful_exists {α : Type} (value : Except String α) (test : α → Bool)
    (success : value.toOption.map test = some true) :
    ∃ result,value = .ok result ∧ test result = true := by
  cases value with
  | error message => cases success
  | ok result => exact ⟨result,rfl,Option.some.inj success⟩

/-- Actual lowering derives the complete fixed schedule from the unchanged admitted input.
No caller supplies a scan schedule or either consumer selection. -/
theorem original_two_load_schedule :
    ∃ (result : Result) (event : BlockScanEvent),Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ sigAbiOk function.sig = true ∧
      result.blockScans.size = 1 ∧ event ∈ result.blockScans.toList ∧ ActualSchedule event := by
  have actual := observed_true
  unfold observed at actual
  obtain ⟨result,run,actual⟩ := successful_exists (Stock.lower function) _ actual
  simp only [Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq] at actual
  obtain ⟨⟨⟨⟨size,scope⟩,dominated⟩,abi⟩,event,events,schedule⟩ := actual
  exact ⟨result,event,run,lowerScope_of scope,dominated_of dominated,abi,size,events,schedule⟩

end Backend.Stock.Proof.AcquireTwoLoadPrefix

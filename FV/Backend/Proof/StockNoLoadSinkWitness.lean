import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.StockNoLoadSink
import FV.Backend.Proof.LowerDecide
import FV.E2E.StockDivFixtures

namespace Backend.Stock.Proof.SinkRules.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Isle.Interp.RuleFrame
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The original nine arguments and explicit stack slot are retained. The
division's result is unused: the source returns an original argument instead. -/
def function : Clif.Function :=
  let original := E2E.StockDivNIWitness.function .defaultI64 .sdiv
  { original with name := "stock_unused_div_no_sink", blocks := original.blocks.map fun b =>
    { b with term := .ret [1] } }

private def built : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)

private theorem built_run : Stock.buildCtx function = .ok built := by rfl

attribute [local semireducible] Isle.Aarch64.program in
private theorem no_loads : NoLoadData built.1 := by
  intro i info found fmt fields load decoded
  have member : info ∈ built.1.insts.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  have table : built.1.insts.toList = [built.1.insts[0]!,built.1.insts[1]!] := by rfl
  rw [table] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have data : ∃ values, (built.1.insts[0]!).data = .data 152 2 values := ⟨_,rfl⟩
    obtain ⟨values,data⟩ := data
    rcases load with rfl | rfl <;> simp [Backend.sem, data] at decoded
  · have data : (built.1.insts[1]!).data = .op .unit := rfl
    simp [Backend.sem, data] at decoded

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

private def observeResult (input : State)
    (result : Except String (Option V × State × List RuleId)) : Bool :=
  match result with
  | .error _ => false
  | .ok (out,next,_) => out.isSome && decide (input.demand[100]! = 0) &&
      decide (input.sunk[0]! = false) && decide (next.base.emitted.size > input.base.emitted.size)

private def observed : Bool := observeResult (scanState built.2.2 0)
  (Stock.runTerm built.1 "lower" [.inst 0] (scanState built.2.2 0))

private theorem observed_true : observed = true := by native_decide

private theorem result_witness {input : State}
    {result : Except String (Option V × State × List RuleId)}
    (checked : observeResult input result = true) :
    ∃ out next trace, result = .ok (some out,next,trace) ∧
      input.demand[100]! = 0 ∧ input.sunk[0]! = false ∧
      next.base.emitted.size > input.base.emitted.size := by
  cases result with
  | error message => cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    simp only [observeResult, Bool.and_eq_true, decide_eq_true_eq] at checked
    cases out with
    | none => simp at checked
    | some out => exact ⟨out,next,trace,rfl,checked.1.1.2,checked.1.2,checked.2⟩

/-- A real unused division with original stack arguments emits code. Its
complete helper execution inhabits the generic no-load frame without demand. -/
theorem unused_division_witness : ∃ out next trace,
    Stock.buildCtx function = .ok built ∧ LowerScope function ∧ NoLoadData built.1 ∧
    Stock.runTerm built.1 "lower" [.inst 0] (scanState built.2.2 0) = .ok (some out,next,trace) ∧
    (scanState built.2.2 0).demand[100]! = 0 ∧ (scanState built.2.2 0).sunk[0]! = false ∧
    next.base.emitted.size > (scanState built.2.2 0).base.emitted.size ∧
    next.sunk = (scanState built.2.2 0).sunk := by
  obtain ⟨out,next,trace,run,demand,sunk,growth⟩ := result_witness observed_true
  have frame := @no_load_lower built.1 no_loads [.inst 0] (scanState built.2.2 0) next (some out) trace run
  exact ⟨out,next,trace,built_run,scope,no_loads,run,demand,sunk,growth,frame⟩

end Backend.Stock.Proof.SinkRules.Witness

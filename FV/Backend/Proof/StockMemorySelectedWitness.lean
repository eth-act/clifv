import FV.Backend.Proof.StockMemorySelected
import FV.Backend.Proof.StockMemoryRecordWitness

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem RecordInput.selected (input : RecordInput) : input.step.rules.getLast? = some rule_lower_2610.id := by
  obtain ⟨receipt⟩ := stock_lower_record_selection input.run input.events input.records input.recorded input.emitted
  have same := Except.ok.inj (receipt.rootRun.symm.trans input.rootRun)
  have trace := congrArg (fun q => q.2.2) same
  change receipt.fired = input.trace.toList ++ [1043] at trace
  rw [receipt.rules,trace]
  simp [rule_lower_2610]

/-- The actual full lowering inhabits selected-ID-to-typed-receipt transfer;
both original metadata matching and named-root execution are exercised. -/
theorem selected_receipts_witness :
    ∃ (input : RecordInput) (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
      flags.endianness ≠ some .big ∧
      Stock.runTerm input.event.ctx "lower" [.inst input.record.inst] (scanState input.record.input input.record.inst) =
        .ok (some out,next,trace) ∧
      (evalExpr program (Stock.sem input.event.ctx) {} 999999 rule_lower_2610.rhs
        (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run
        (scanState input.record.input input.record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  obtain ⟨input⟩ := record_input
  obtain ⟨little,out,next,trace,rhsTrace,root,rhs⟩ := stock_lower_load_selected_receipts input.run scope
    input.events input.records input.source input.clif input.recorded input.emitted input.selected
  exact ⟨input,out,next,trace,rhsTrace,little,root,rhs⟩

end Backend.Stock.Memory.LoadFixture

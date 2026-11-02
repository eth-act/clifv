import FV.Backend.Proof.StockMemoryExtLoadSource
import FV.Backend.Proof.StockSelectionReceipts

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Original metadata determines the retained extending-load root and its actual
match/RHS receipt. The caller supplies no selected-root certificate. -/
theorem stock_lower_extending_load_selected_receipts (kind : Kind) {ty : Clif.Ty} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    flags.endianness ≠ some .big ∧
      ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
          .ok (some out,next,trace) ∧
        (evalExpr program (Stock.sem event.ctx) {} 999999 kind.root.rhs
          (env3 (.value x) (.op (.memFlags flags)) (.int 0))).run
          (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have ruleEq := stock_selected_extending_load_rule kind inv source clif receipt.selected
  obtain ⟨little,data⟩ := extending_load_source_data kind inv source clif
  have bound : (program.rulesOf T.lower.id).length ≤ 999995 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuelBound := receipt.selected.fuelBound
  have enough : 2 ≤ receipt.selected.matchFuel := by omega
  obtain ⟨n,fuelEq⟩ : ∃ n,receipt.selected.matchFuel = n+2 := ⟨receipt.selected.matchFuel-2,by omega⟩
  have actualMatch := receipt.selected.matchedRun
  rw [ruleEq,fuelEq] at actualMatch
  have expected := stock_match_extending_load data_program kind event.ctx (cfg := {}) source data little
    (scanState record.input record.inst) #[] n
  have same := Except.ok.inj (actualMatch.symm.trans expected)
  have envEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  have traceEq := congrArg (fun q => q.2.2) same
  change receipt.selected.matched = scanState record.input record.inst at stateEq
  change receipt.selected.matchTrace = #[] at traceEq
  have evaluated := receipt.selected.rhsRun
  rw [ruleEq,envEq,stateEq,traceEq] at evaluated
  exact ⟨little,receipt.out,receipt.next,receipt.fired,receipt.selected.rhsTrace,receipt.rootRun,evaluated⟩

end Backend.Stock.Memory.ExtendedRoots

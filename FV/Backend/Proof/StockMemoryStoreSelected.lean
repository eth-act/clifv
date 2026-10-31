import FV.Backend.Proof.StockMemoryStoreDispatch

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual retained stores derive complete match and RHS receipts from original source facts. -/
theorem stock_lower_integer_store_selected_receipts_offset (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer : Nat} {flags : Clif.MemFlags} {offset : Int}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer offset))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    flags.endianness ≠ some .big ∧
      ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
          .ok (some out,next,trace) ∧
        (evalExpr program (Stock.sem event.ctx) {} 999999 kind.root.rhs
          (env4 (.value value) (.value pointer) (.op (.memFlags flags)) (.int offset))).run
          (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have inv := (stock_lower_record_context run scope events).1
  have chosen := stock_selected_integer_store_rule_offset kind inv source clif typed receipt.selected
  obtain ⟨little,data⟩ := integer_store_source_data_offset kind inv source clif
  have bound : (program.rulesOf T.lower.id).length ≤ 999977 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have fuelBound := receipt.selected.fuelBound
  have enough : 20 ≤ receipt.selected.matchFuel := by omega
  obtain ⟨n,fuelEq⟩ : ∃ n,receipt.selected.matchFuel = n+20 :=
    ⟨receipt.selected.matchFuel-20,by omega⟩
  have matched := receipt.selected.matchedRun
  rw [chosen,fuelEq] at matched
  have expected := stock_match_integer_store_offset data_program kind event.ctx (cfg := {}) source typed data little
    (scanState record.input record.inst) #[] n
  have same := Except.ok.inj (matched.symm.trans expected)
  have envEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  have traceEq := congrArg (fun q => q.2.2) same
  change receipt.selected.matched = scanState record.input record.inst at stateEq
  change receipt.selected.matchTrace = #[] at traceEq
  have evaluated := receipt.selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at evaluated
  exact ⟨little,receipt.out,receipt.next,receipt.fired,receipt.selected.rhsTrace,receipt.rootRun,evaluated⟩

/-- Preserve the original zero-offset theorem variant. -/
theorem stock_lower_integer_store_selected_receipts (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {value pointer : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.store kind.sourceOp ty flags value pointer 0))
    (typed : kind.sourceOp = .store → event.ctx.valueType? value = some (.int kind.width.bits))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    flags.endianness ≠ some .big ∧
      ∃ (out : V) (next : State) (trace : List RuleId) (rhsTrace : Array RuleId),
        Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) =
          .ok (some out,next,trace) ∧
        (evalExpr program (Stock.sem event.ctx) {} 999999 kind.root.rhs
          (env4 (.value value) (.value pointer) (.op (.memFlags flags)) (.int 0))).run
          (scanState record.input record.inst,#[]) = .ok (some out,next,rhsTrace) := by
  exact stock_lower_integer_store_selected_receipts_offset kind run scope events records source clif typed recorded emitted

end Backend.Stock.Memory.StoreRoots

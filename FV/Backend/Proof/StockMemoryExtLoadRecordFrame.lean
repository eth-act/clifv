import FV.Backend.Proof.StockMemoryExtLoadSelected
import FV.Backend.Proof.StockTerminalRoots

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- An actual parameter-pointer load retains every sunk bit through source
selection, nested address helpers, result binding and final physical copies.
No selected-ID, code-shape or no-load-context certificate is required. -/
theorem stock_lower_extending_load_sunk_eq (kind : Kind) {ty : Clif.Ty} {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {x nreg : Nat} {flags : Clif.MemFlags}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0))
    (parameter : event.ctx.defInst? x = none)
    (pointer : event.ctx.valueReg? x = some (.vreg nreg .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    record.output.state.sunk = record.input.sunk := by
  obtain ⟨little,out,next,trace,rhsTrace,rootRun,evalRun⟩ := stock_lower_extending_load_selected_receipts kind
    run scope events records source clif recorded emitted
  obtain ⟨computed,actual⟩ := stock_parameter_extending_load_rhs data_program kind event.ctx (cfg := {}) rfl
    parameter pointer flags (scanState record.input record.inst) #[] 999879
  have equal := Except.ok.inj (evalRun.symm.trans actual)
  have nextEq := congrArg (fun q => q.2.1) equal
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have same := Except.ok.inj (receipt.rootRun.symm.trans rootRun)
  have sameNext := congrArg (fun q => q.2.1) same
  dsimp only at sameNext nextEq
  have unchanged := (congrArg State.sunk receipt.state).trans (Coverage.bindResults_noSink receipt.binding)
  rw [sameNext,nextEq] at unchanged
  have normalized : (scanState record.input record.inst).sunk = record.input.sunk := by
    unfold scanState
    dsimp only
    split <;> rfl
  exact unchanged.trans normalized

end Backend.Stock.Memory.ExtendedRoots

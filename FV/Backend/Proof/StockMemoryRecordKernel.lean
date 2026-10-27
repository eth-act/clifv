import FV.Backend.Proof.StockMemoryInput

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private instance : DecidableEq V := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq

theorem record_observed :
    (Stock.lower function).toOption.map (fun result =>
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 1 && record.input.base.nextVreg == 194 &&
        decide ((event.ctx.insts[record.inst]?).map (fun info => (info.clif,info.results)) =
          some (some (.load .load .i32 flags 0 0),[2])) &&
        decide (event.ctx.valueReg? 2 = some (.vreg 193 .int)) &&
        decide (event.ctx.valueReg? 0 = some (.vreg 192 .int)) &&
        decide (event.ctx.defInst? 0 = none) &&
        record.output.step.any (fun step => step.decision == .emitted) &&
        ((evalExpr program (Stock.sem event.ctx) {} 120 rule_lower_2610.rhs
          (env3 (.value 0) (.op (.memFlags flags)) (.int 0))).run
          (scanState record.input record.inst,#[])).toOption.any (fun evaluated =>
            decide (evaluated.1 = some (.regsVec [[.vreg 194 .int]])) &&
            decide ((Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst)).toOption =
              some (evaluated.1,evaluated.2.1,evaluated.2.2.toList ++ [1043])))))) = some true := by
  decide +kernel

end Backend.Stock.Memory.LoadFixture

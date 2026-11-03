import FV.Backend.Lowering.StockGeneralArgsLoopCfg7

/-! The legacy loop class with plain `band` conditions (#140, CB-15).

`GeneralLoopCfg6` (CB-14c) with the conditions of `GeneralArgsLoopCfg7.conditionEligible`: a
condition of `GeneralArgsLoopCfg5`, or a plain `band`. `brif` successors take no arguments; jumps
may pass any arguments, and `br_table` successors take none, as in `GeneralLoopCfg6`. The checker
publishes the unsplit code of the actual Stock lowering, so the class keeps the legacy
single-vector interface (`Scalar.Domain`). -/

namespace Backend.Stock.GeneralLoopCfg7
open Backend.Proof.Driver
set_option autoImplicit false

/-- `GeneralLoopCfg6.controlEligible` with `GeneralArgsLoopCfg7.conditionEligible`: branches with
empty arguments, each target an existing nonentry block; the other terminators as there. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .brif c yes no => GeneralArgsLoopCfg7.conditionEligible f b c && yes.args.isEmpty &&
    no.args.isEmpty && ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | term => GeneralLoopCfg6.controlEligible f b term

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralLoopCfg6.sourceLeafEligible` with the terminators of `controlLeafEligible`. Bodies and
ABI are as there. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the unsplit code of the actual Stock lowering. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.GeneralLoopCfg7

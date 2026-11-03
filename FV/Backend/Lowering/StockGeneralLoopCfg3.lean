import FV.Backend.Lowering.StockGeneralArgsLoopCfg3

/-! The legacy loop class with plain `i8` conditions (#140, CB-12).

`GeneralLoopCfg2` (CB-11) is the legacy (unsplit-code, empty `brif` arguments) class of wide
conditions. Here a `brif` condition is any condition of `GeneralArgsLoopCfg3.conditionEligible`:
a condition of `GeneralArgsLoopCfg2`, or a narrow condition (an `i8` parameter, or an `i8` result
of a statement that is not an `icmp`, a `band` or a `uextend`, lowered to `tst` and `b.ne`). Its
successors take no arguments. Every edge enters an existing nonentry block, so back edges and
self loops are selected. Jumps may pass any arguments. The checker publishes the unsplit code of
the actual Stock lowering, so the class keeps the legacy single-vector interface
(`Scalar.Domain`). -/

namespace Backend.Stock.GeneralLoopCfg3
open Backend.Proof.Driver
set_option autoImplicit false

/-- `GeneralLoopCfg2.controlEligible` with `GeneralArgsLoopCfg3.conditionEligible`: jumps with
any arguments, returns, and branches with empty arguments, each target an existing nonentry
block. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => GeneralArgsLoopCfg3.conditionEligible f b c && yes.args.isEmpty &&
    no.args.isEmpty && ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralLoopCfg2.sourceLeafEligible` with the conditions of
`GeneralArgsLoopCfg3.conditionEligible`. Bodies and ABI are as there. -/
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

end Backend.Stock.GeneralLoopCfg3

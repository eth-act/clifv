import FV.Backend.Lowering.StockGeneralArgsLoopCfg5

/-! The legacy loop class with one-bit tests and zero extensions as conditions (#140, CB-13).

`GeneralLoopCfg4` (CB-12b) is the legacy (unsplit-code, empty `brif` arguments) class of the
conditions of `GeneralArgsLoopCfg4`. Here a `brif` condition is any condition of
`GeneralArgsLoopCfg5.conditionEligible`: a condition of `GeneralArgsLoopCfg4`, a one-bit test, a
zero test of a one-bit mask, a zero extension of a wide comparison, or a plain zero extension. Its
successors take no arguments. Every edge enters an existing nonentry block, so back edges and self
loops are selected. Jumps may pass any arguments. The checker publishes the unsplit code of the
actual Stock lowering, so the class keeps the legacy single-vector interface (`Scalar.Domain`). -/

namespace Backend.Stock.GeneralLoopCfg5
open Backend.Proof.Driver
set_option autoImplicit false

/-- `GeneralLoopCfg4.controlEligible` with `GeneralArgsLoopCfg5.conditionEligible`: jumps with
any arguments, returns, and branches with empty arguments, each target an existing nonentry
block. -/
def controlEligible (f : Clif.Function) (b : Clif.Block) : Clif.Terminator → Bool
  | .jump bc => ParameterLoopCfg.targetNonentry f bc
  | .ret _ => true
  | .brif c yes no => GeneralArgsLoopCfg5.conditionEligible f b c && yes.args.isEmpty &&
    no.args.isEmpty && ParameterLoopCfg.targetNonentry f yes && ParameterLoopCfg.targetNonentry f no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) (b : Clif.Block) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f b term

/-- `GeneralLoopCfg4.sourceLeafEligible` with the conditions of
`GeneralArgsLoopCfg5.conditionEligible`. Bodies and ABI are as there. -/
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

end Backend.Stock.GeneralLoopCfg5

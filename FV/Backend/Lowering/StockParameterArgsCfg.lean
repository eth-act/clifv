import FV.Backend.Lowering.StockParameterCfg
import FV.Backend.Lowering.StockConditionalArgsCfg
import FV.Backend.EdgeSplit

namespace Backend.Stock.ParameterArgsCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `ParameterCfg.controlEligible`, where a parameter branch may pass block arguments. -/
def controlEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .jump bc => ParameterCfg.targetAfter f bi bc
  | .ret _ => true
  | .brif c yes no => ParameterCfg.parameterEligible f c &&
    ParameterCfg.targetAfter f bi yes && ParameterCfg.targetAfter f bi no
  | _ => false

/-- As `controlEligible`, and a nonentry block may also end in `trap`. -/
def controlLeafEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .trap _ => bi != 0
  | term => controlEligible f bi term

/-- Ranked forward CFGs whose parameter branches may pass block arguments, in a lowered order
without critical-edge nodes. -/
def sourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible &&
  ConditionalArgsCfg.originalOrder f

def sourceOk (f : Clif.Function) : Bool :=
  sourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the actual edge split of the actual Stock lowering. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => decide (split.code = vc)
    | .error _ => false

end Backend.Stock.ParameterArgsCfg

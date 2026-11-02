import FV.Backend.Lowering.StockParameterArgsCfg

namespace Backend.Stock.ParameterArgsCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- `sourceLeafEligible` with no restriction on critical edges: parameter branches may pass block
arguments to original or critical-edge successors. -/
def anySourceLeafEligible (f : Clif.Function) : Bool :=
  f.blocks.zipIdx.all (fun (b,bi) => controlLeafEligible f bi b.term) &&
  f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
  f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible

def anySourceOk (f : Clif.Function) : Bool :=
  anySourceLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the actual edge split of the actual Stock lowering. -/
def anyCheck (f : Clif.Function) (vc : VCode) : Bool :=
  anySourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => decide (split.code = vc)
    | .error _ => false

end Backend.Stock.ParameterArgsCfg

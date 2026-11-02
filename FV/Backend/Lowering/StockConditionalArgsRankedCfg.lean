import FV.Backend.Lowering.StockConditionalArgsCfg
import FV.Backend.Lowering.StockForwardCfg
import FV.Backend.EdgeSplit

namespace Backend.Stock.ConditionalArgsCfg
open Backend.Proof.Driver
set_option autoImplicit false

/-- A branch target after the entry block. -/
def laterTarget (f : Clif.Function) (bc : Clif.BlockCall) : Bool :=
  match f.blocks.findIdx? (·.id == bc.block) with
  | some target => decide (0 < target)
  | none => false

/-- Wide entry-parameter branches that may pass block arguments, with ranked forward tails that
jump, return or end in `trap`. -/
def rankedLeafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      laterTarget f yes && laterTarget f no &&
      rest.zipIdx.all (fun (b,bi) => Backend.Stock.ForwardCfg.controlLeafEligible f (bi+1) b.term) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible &&
      originalOrder f
    | _ => false
  | _ => false

def rankedSourceOk (f : Clif.Function) : Bool :=
  rankedLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

/-- The published code is the actual edge split of the actual Stock lowering. -/
def rankedCheck (f : Clif.Function) (vc : VCode) : Bool :=
  rankedSourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => match splitEdgesChecked result.code result.edgeArgs with
    | .ok split => decide (split.code = vc)
    | .error _ => false

end Backend.Stock.ConditionalArgsCfg

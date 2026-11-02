import FV.Backend.Lowering.StockConditionalCfg
import FV.Backend.Lowering.StockForwardCfg

namespace Backend.Stock.ConditionalCfg
open Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

def rankedEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      targetEligible f yes && targetEligible f no &&
      rest.zipIdx.all (fun (b,bi) => Backend.Stock.ForwardCfg.controlEligible f (bi+1) b.term) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false
/-- The same class when tail blocks may also end in `trap`. -/
def rankedLeafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      targetEligible f yes && targetEligible f no &&
      rest.zipIdx.all (fun (b,bi) => Backend.Stock.ForwardCfg.controlLeafEligible f (bi+1) b.term) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false
def rankedSourceOk (f : Clif.Function) : Bool :=
  rankedLeafEligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig

def rankedCheck (f : Clif.Function) (vc : VCode) : Bool :=
  rankedSourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ConditionalCfg

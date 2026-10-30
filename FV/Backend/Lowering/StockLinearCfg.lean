import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.LinearCfg
set_option autoImplicit false

/-- A complete three-block scalar chain. Values may be inherited directly;
bodies and successor argument lists need not be empty. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,middle,target] =>
    match entry.term,middle.term,target.term with
    | .jump first,.jump second,.ret _ =>
      first.block == middle.id && second.block == target.id &&
      entry.id != middle.id && entry.id != target.id && middle.id != target.id &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _,_,_ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && Backend.Proof.Driver.lowerScopeB f &&
    Backend.Proof.Driver.dominatedB f && Backend.sigAbiOk f.sig

/-- Validate the actual Stock artifact against the proved source class. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.LinearCfg

import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.ForwardCfg
set_option autoImplicit false

/-- A jump strictly advances the original source block index; returns end the
path. Unreachable source blocks remain allowed. -/
def controlEligible (f : Clif.Function) (bi : Nat) : Clif.Terminator → Bool
  | .jump bc => match f.blocks.findIdx? (·.id == bc.block) with
    | some target => decide (bi < target)
    | none => false
  | .ret _ => true
  | _ => false

/-- Arbitrary-length scalar jump/return graphs, with a jumping entry. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: _ => match entry.term with
    | .jump _ =>
      f.blocks.zipIdx.all (fun (b,bi) => controlEligible f bi b.term) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && Backend.Proof.Driver.lowerScopeB f &&
    Backend.Proof.Driver.dominatedB f && Backend.sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ForwardCfg

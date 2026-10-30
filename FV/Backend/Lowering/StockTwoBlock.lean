import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.TwoBlock
set_option autoImplicit false

def entryEligible (stm : Clif.Stmt) : Bool :=
  Scalar.maskMixedBodyEligible stm &&
    match stm.inst with | .iconst .. | .nop => true | _ => false

/-- First direct CFG production class. Original source checks and fallback
remain separate; successor arguments may be nonempty. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,target] =>
    match entry.term with
    | .jump bc =>
      match target.term with
      | .ret _ =>
        bc.block == target.id && entry.id != target.id &&
        entry.body.all entryEligible && target.body.all Scalar.maskMixedBodyEligible &&
        entry.body.all (fun stm => stm.results.all bc.args.contains) &&
        f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && Backend.Proof.Driver.lowerScopeB f &&
    Backend.Proof.Driver.dominatedB f && Backend.sigAbiOk f.sig

/-- Replay the actual Stock result; single-successor compatibility is derived
by the source-class proof, rather than rejecting nonempty argument vectors. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.TwoBlock

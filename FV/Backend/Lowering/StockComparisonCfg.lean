import FV.Backend.Lowering.StockConditionalCfg

namespace Backend.Stock.ComparisonCfg
set_option autoImplicit false

/-- `stm` defines `condition` by an `icmp` of two entry parameters of one
wide type: both `.i32` or both `.i64`. -/
def comparisonEligible (entry : Clif.Block) (condition : Nat) (stm : Clif.Stmt) : Bool :=
  stm.results.contains condition && match stm.inst with
    | .icmp _ _ x y =>
      (entry.params.contains (x,.i32) && entry.params.contains (y,.i32)) ||
        (entry.params.contains (x,.i64) && entry.params.contains (y,.i64))
    | _ => false

/-- Branches on a direct entry comparison of two entry parameters into return
or trap blocks. Every nonentry block has no parameters, and both targets carry
no arguments, preserving the existing legacy edge-copy interface. -/
def leafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.body.any (comparisonEligible entry condition) &&
      ConditionalCfg.targetEligible f yes && ConditionalCfg.targetEligible f no &&
      rest.all (fun b => b.params.isEmpty && match b.term with | .ret _ | .trap _ => true | _ => false) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  leafEligible f && Backend.Proof.Driver.lowerScopeB f &&
    Backend.Proof.Driver.dominatedB f && Backend.sigAbiOk f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc)

end Backend.Stock.ComparisonCfg

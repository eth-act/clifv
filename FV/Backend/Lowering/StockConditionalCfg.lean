import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.ConditionalCfg
set_option autoImplicit false

/-- Initial compatible conditional edges carry inherited values directly;
nonempty per-successor vectors retain their separate migration obligation. -/
def targetEligible (f : Clif.Function) (bc : Clif.BlockCall) : Bool :=
  bc.args.isEmpty && match f.blocks.findIdx? (·.id == bc.block) with
    | some target => decide (0 < target)
    | none => false

/-- Wide entry-parameter branches into scalar return blocks. Every nonentry
block has no parameters, preserving the existing legacy edge-copy interface. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      targetEligible f yes && targetEligible f no &&
      rest.all (fun b => b.params.isEmpty && match b.term with | .ret _ => true | _ => false) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible
    | _ => false
  | _ => false

/-- The same class when each nonentry block returns or ends in `trap`. -/
def leafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition yes no =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      targetEligible f yes && targetEligible f no &&
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

end Backend.Stock.ConditionalCfg

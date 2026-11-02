import FV.Backend.Lowering.StockScalar
import FV.Backend.StockArithmeticCheck

namespace Backend.Stock.ConditionalArgsCfg
set_option autoImplicit false

/-- The lowered block order keeps every node an original block: no edge is critical, so
each `brif` argument vector stays with its original successor. -/
def originalOrder (f : Clif.Function) : Bool :=
  match blockOrder f with
  | .ok order => order.nodes.all fun | .original _ => true | .edge .. => false
  | .error _ => false

/-- Wide entry-parameter branches that may pass block arguments to blocks that return or end
in `trap`. Nonentry blocks may have parameters. -/
def leafEligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | entry :: rest => match entry.term with
    | .brif condition _ _ =>
      entry.params.any (fun (value,ty) => value == condition && (ty == .i32 || ty == .i64)) &&
      rest.all (fun b => match b.term with | .ret _ | .trap _ => true | _ => false) &&
      f.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) &&
      f.sig.params.all Scalar.narrowAbiEligible && f.sig.returns.all Scalar.narrowAbiEligible &&
      originalOrder f
    | _ => false
  | _ => false

end Backend.Stock.ConditionalArgsCfg

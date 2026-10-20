import FV.Backend.Proof.StockSelectNarrowComparisonShape
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- All original scalar comparison widths derive their decoded condition
from actual first-match execution, without an operand-classification premise. -/
theorem stock_select_comparison_condition_shape {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (cc : Clif.IntCC) {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width)) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace)) :
    CondShape out (fun _ => True) := by
  cases ty
  · exact stock_select_narrow_comparison_condition_shape inv cc false typeX typeY enough run
  · exact stock_select_narrow_comparison_condition_shape inv cc true typeX typeY enough run
  · exact stock_select_wide_comparison_condition_shape inv cc false typeX typeY enough run
  · exact stock_select_wide_comparison_condition_shape inv cc true typeX typeY enough run
  · simp [Clif.Ty.width] at width
end Backend.Stock.Proof.ScalarSelect

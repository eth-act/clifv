import FV.Backend.Proof.StockSelectNonzeroConditionShape
import FV.Backend.Proof.StockConditionPrefix
import FV.Backend.Proof.StockSelectConditionInvertShape
import FV.Backend.Proof.StockCmpMatchedZero
import FV.Backend.Proof.StockCmpZero32RuleCalls
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- Every actual scalar equality/inequality-to-zero RHS derives a decoded
condition, including narrow extensions, masking and real inversion. -/

theorem stock_select_zero_rhs_prefix {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (left nonzero : Bool) {x y n : Nat}
    (typeX : ctx.valueType? x = some (.int ty.width))
    (typeY : ctx.valueType? y = some (.int ty.width))
    {st next : State} {tr trace : Array RuleId} {out : V}
    (rhs : (evalExpr program (Stock.sem ctx) {} (n+240) (cmpZeroRule left nonzero).rhs
      #[some (.value (if left then y else x))]).run (st,tr) = .ok (some out,next,trace)) :
    ∃ code,Frag st.base next.base code := by
  have typed : ctx.valueType? (if left then y else x) = some (.int ty.width) := by
    cases left <;> assumption
  cases nonzero
  · have equalRhs : (cmpZeroRule left false).rhs = rule_inst_5170.rhs := by cases left <;> rfl
    rw [equalRhs] at rhs
    obtain ⟨emitFuel,inverseFuel,raw,middle,middleTrace,enoughEmit,enoughInverse,emitter,inversion⟩ :=
      stock_cmp_zero32_eq_rhs_calls data_program ctx (if left then y else x) n rhs
    have unchanged := (stock_select_condition_invert_shape enoughInverse
      (stock_select_nonzero_actual_condition_shape inv width enoughEmit typed emitter) inversion).2
    rw [unchanged]
    exact stock_select_nonzero_prefix inv width enoughEmit typed emitter
  · have equalRhs : (cmpZeroRule left true).rhs = rule_inst_5172.rhs := by cases left <;> rfl
    rw [equalRhs] at rhs
    obtain ⟨emitFuel,enoughEmit,emitter⟩ :=
      stock_cmp_zero32_ne_rhs_calls data_program ctx (if left then y else x) n rhs
    exact stock_select_nonzero_prefix inv width enoughEmit typed emitter


end Backend.Stock.Proof.ScalarSelect

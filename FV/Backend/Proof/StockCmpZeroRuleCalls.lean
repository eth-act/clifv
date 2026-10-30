import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselCtlTry
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- The actual inequality-to-zero RHS calls the original nonzero helper;
the full state and trace are the helper's state and trace. -/
theorem stock_cmp_zero_ne_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (x n : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_5172.rhs
      #[some (.value x)]).run (st,tr) = .ok (some out,next,trace)) :
    ∃ fuel,200 ≤ fuel ∧ ApplyInternal p (Stock.sem ctx) {} fuel 123 651
      [.value x] (st,tr) out (next,trace) := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_inst_5172] at run
  simp only [show (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) from rfl,Option.some.injEq] at *
  isel_destruct
  subst_vars
  exact ⟨n+218,by omega,by assumption⟩
/-- Equality-to-zero executes both real helper calls, including inversion;
no helper success certificate is supplied by the caller. -/
theorem stock_cmp_zero_eq_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (x n : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_5170.rhs
      #[some (.value x)]).run (st,tr) = .ok (some out,next,trace)) :
    ∃ (emitFuel inverseFuel : Nat) (raw : V) (middle : State) (middleTrace : Array RuleId),
      200 ≤ emitFuel ∧ 39 ≤ inverseFuel ∧
      ApplyInternal p (Stock.sem ctx) {} emitFuel 123 651 [.value x]
        (st,tr) raw (middle,middleTrace) ∧
      ApplyInternal p (Stock.sem ctx) {} inverseFuel 123 649 [raw]
        (middle,middleTrace) out (next,trace) := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_inst_5170] at run
  simp only [show (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) from rfl,Option.some.injEq] at *
  isel_destruct
  subst_vars
  rename_i raw middle inverseCall emitCall
  exact ⟨n+216,by omega,n+218,by omega,raw,middle.1,middle.2,emitCall,inverseCall⟩
end Backend.Stock.Proof.ScalarCmp

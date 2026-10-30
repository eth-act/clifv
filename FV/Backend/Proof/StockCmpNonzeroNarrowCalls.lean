import FV.Backend.Proof.StockCmpZeroValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Actual narrow nonzero RHS success derives the original zero-extension call
and the exact32-bit condition, including complete intermediate state and trace. -/
theorem stock_cmp_nonzero_narrow_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (x : Nat) (ty : CTy) (n : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_4977.rhs
      #[some (.ty ty),some (.value x)]).run (st,tr) = .ok (some out,next,trace)) :
    ∃ (fuel : Nat) (value : V),60 ≤ fuel ∧
      ApplyInternal p (Stock.sem ctx) {} fuel 27 556 [.value x] (st,tr) value (next,trace) ∧
      out = .data 123 1 [value,.data 93 0 []] := by
  cases hp
  isel_inv [*,rule_inst_4977,sem_mkData] at run
  simp only [show (#[some (.ty ty),some (.value x)] : Isle.Interp.Env V)[1]? =
    some (some (.value x)) from rfl,Option.some.injEq] at *
  isel_destruct
  subst_vars
  exact ⟨n+216,by omega,by assumption⟩
end Backend.Stock.Proof.ScalarCmp

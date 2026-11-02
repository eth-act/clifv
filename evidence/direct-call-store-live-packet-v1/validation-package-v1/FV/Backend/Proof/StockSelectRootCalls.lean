import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselCtlTry
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
/-- Actual original select-root match environment. -/
def originalSelectEnv (w c x y : Nat) : Isle.Interp.Env V :=
  #[some (.ty (.int w)),some (.value c),some (.value x),some (.value y)]
/-- Internal original650 condition producer,659 consumer and output calls. -/
def OriginalSelectRootCalls (p : Program) (ctx : Ctx) (w c x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ emitFuel selectFuel condition middle emitTrace value produced selectTrace,
    400 ≤ emitFuel ∧ 319 ≤ selectFuel ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 123 650 [.value c]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int w),condition,.value x,.value y] (middle,emitTrace) value (produced,selectTrace) ∧
    Stock.externCtor ctx T.output [value] produced = .ok (out,next)
/-- Original select RHS supplies its actual condition producer, consumer and
external output, with full intermediate Stock scheduling states and real fuel. -/
theorem stock_original_select_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (w c x y : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2267.rhs
      (originalSelectEnv w c x y)).run (st,tr) = .ok (some out,next,trace)) :
    OriginalSelectRootCalls p ctx w c x y st next tr trace out := by
  have get0 : (originalSelectEnv w c x y)[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (originalSelectEnv w c x y)[1]? = some (some (.value c)) := rfl
  have get2 : (originalSelectEnv w c x y)[2]? = some (some (.value x)) := rfl
  have get3 : (originalSelectEnv w c x y)[3]? = some (some (.value y)) := rfl
  cases hp
  isel_inv [*,rule_lower_2267,sem_ctor] at run
  isel_destruct
  subst_vars
  unfold OriginalSelectRootCalls
  rename_i value nextState produced condition middle outputCall selectCall emitCall
  exact ⟨999992,999995,condition,middle.1,middle.2,value,produced.1,produced.2,
    by decide,by decide,selectCall,emitCall,outputCall⟩
end Backend.Stock.Proof.ScalarSelect

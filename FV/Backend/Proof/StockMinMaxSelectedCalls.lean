import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.StockMinMaxSourceMatch
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
def MinMaxRootCalls (p : Program) (ctx : Ctx) (unsigned maximum : Bool) (w x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ emitFuel selectFuel condition middle emitTrace value produced selectTrace,
    200 ≤ emitFuel ∧ 279 ≤ selectFuel ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx (minmaxComparison unsigned maximum)) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int w),condition,.value x,.value y] (middle,emitTrace) value (produced,selectTrace) ∧
    Stock.externCtor ctx T.output [value] produced = .ok (out,next)
/-- The actual min/max RHS exposes its real652/659 calls and external output,
including full intermediate Stock states and their actual interpreter fuel. -/
theorem stock_minmax_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (unsigned maximum : Bool) (w x y : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 (minmaxRule unsigned maximum).rhs (minmaxEnv w x y)).run
      (st,tr) = .ok (some out,next,trace)) : MinMaxRootCalls p ctx unsigned maximum w x y st next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  have get0 : (minmaxEnv w x y)[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (minmaxEnv w x y)[1]? = some (some (.value x)) := rfl
  have get2 : (minmaxEnv w x y)[2]? = some (some (.value y)) := rfl
  cases unsigned <;> cases maximum
  all_goals cases hp
  all_goals isel_inv [*,minmaxRule,minmaxComparison,sem_ctor,sem_mkData,
    rule_lower_1222,rule_lower_1224,rule_lower_1226,rule_lower_1228] at run
  all_goals isel_destruct
  all_goals subst_vars
  all_goals unfold MinMaxRootCalls
  all_goals rename_i value nextState produced condition middle outputCall selectCall emitCall
  all_goals exact ⟨999992,999995,condition,middle.1,middle.2,value,produced.1,produced.2,
    by decide,by decide,emitCall,selectCall,outputCall⟩
/-- Actual original-source selection derives the unique min/max root, canonical
environment, unchanged match state and all real RHS calls internally. -/
theorem stock_minmax_selected_calls {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (unsigned maximum : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules) :
    selected.rule = minmaxRule unsigned maximum ∧ selected.env = minmaxEnv ty.width x y ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      MinMaxRootCalls program ctx unsigned maximum ty.width x y st next #[] selected.rhsTrace out := by
  obtain ⟨_,data,type⟩ := stock_minmax_source_data inv unsigned maximum source clif
  have chosen := stock_selected_minmax_rule inv unsigned maximum source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_minmax_match data_program ctx unsigned maximum source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  exact ⟨chosen,envEq.symm,stateEq.symm,traceEq.symm,stock_minmax_rhs_calls data_program ctx unsigned maximum ty.width x y rhs⟩
end Backend.Stock.Proof.ScalarSelect

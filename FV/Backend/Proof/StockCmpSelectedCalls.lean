import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockCmpSourceMatch
import FV.Backend.Proof.StockCmpRootMatch
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def RootCalls (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ emitFuel conditionFuel outputFuel condition middle emitTrace value produced conditionTrace,
    200 ≤ emitFuel ∧ 119 ≤ conditionFuel ∧ 9 ≤ outputFuel ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} conditionFuel 27 715 [condition]
      (middle,emitTrace) value (produced,conditionTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} outputFuel 25 172 [value]
      (produced,conditionTrace) out (next,trace)
/-- Successful actual comparison RHS execution exposes all three real helper
calls and their complete intermediate states, without caller helper certificates. -/
theorem stock_cmp_root_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (x y : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2215.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace)) : RootCalls p ctx cc x y st next tr trace out := by
  have hc : ({} : Config).checkOverlap = false := rfl
  cases hp
  isel_inv [*,rule_lower_2215,cmpEnv,env3] at run
  isel_destruct
  subst_vars
  rename_i value produced condition middle outputCall conditionCall emitCall
  exact ⟨999993,999995,999997,condition,middle.1,middle.2,value,produced.1,produced.2,
    by decide,by decide,by decide,emitCall,conditionCall,outputCall⟩
/-- Original first-match source selection determines its canonical environment,
unchanged match state, original operand type and all real RHS helper calls. -/
theorem stock_cmp_selected_calls {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {cc : Clif.IntCC} {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    (∃ w,ctx.valueType? x = some (.int w)) ∧
      selected.rule = rule_lower_2215 ∧ selected.env = cmpEnv cc x y ∧ selected.matched = st ∧
      selected.matchTrace = #[] ∧ RootCalls program ctx cc x y st next #[] selected.rhsTrace out := by
  obtain ⟨_,data,type⟩ := stock_cmp_source_data inv source clif
  have id := stock_selected_cmp_root inv source clif selected
  have candidate : rule_lower_2215 ∈ program.rulesOf T.lower.id := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate id
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨operandType,envEq,stateEq,traceEq⟩ := stock_cmp_root_match_observed data_program ctx source type data matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at rhs
  exact ⟨operandType,chosen,envEq,stateEq,traceEq,stock_cmp_root_rhs_calls data_program ctx cc x y rhs⟩
end Backend.Stock.Proof.ScalarCmp

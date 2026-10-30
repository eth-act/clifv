import FV.Backend.Proof.StockCmpNarrowActualAllocation
import FV.Backend.Proof.StockCmpSourceMatch
import FV.Backend.Proof.StockCmpRootMatch
import FV.Backend.Proof.StockCmpOutput
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem cmp_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

private theorem value_reg_state (ctx : Ctx) (v : V) (st : State) {w : V} {next : State}
    (run : Stock.externCtor ctx T.value_reg [v] st = .ok (w,next)) : next = st := by
  rw [stock_ctor_baseOnly ctx T.value_reg [v] st (by decide)] at run
  cases v <;> cases run <;> rfl
private theorem output_state (ctx : Ctx) (v : V) (st : State) {w : V} {next : State}
    (run : Stock.externCtor ctx T.output [v] st = .ok (w,next)) : next = st := by
  rw [stock_ctor_baseOnly ctx T.output [v] st (by decide)] at run
  cases v <;> cases run <;> rfl
private def ActualRootCalls (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (x y : Nat)
    (st next : State) (tr trace : Array RuleId) (out : V) : Prop :=
  ∃ emitFuel conditionFuel outputFuel condition middle emitTrace value produced conditionTrace,
    300 ≤ emitFuel ∧ 119 ≤ conditionFuel ∧ 100 ≤ outputFuel ∧
    ApplyInternal p (Stock.sem ctx) {} emitFuel 123 652 [.data 145 (ccIdx cc) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} conditionFuel 27 715 [condition]
      (middle,emitTrace) value (produced,conditionTrace) ∧
    ApplyInternal p (Stock.sem ctx) {} outputFuel 25 172 [value]
      (produced,conditionTrace) out (next,trace)
/-- Successful actual comparison RHS execution exposes all three real helper
calls and their complete intermediate states, without caller helper certificates. -/
private theorem actual_root_rhs_calls {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (x y : Nat) {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} 999999 rule_lower_2215.rhs (cmpEnv cc x y)).run
      (st,tr) = .ok (some out,next,trace)) : ActualRootCalls p ctx cc x y st next tr trace out := by
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
private theorem actual_selected_calls {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {cc : Clif.IntCC} {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    (∃ w,ctx.valueType? x = some (.int w)) ∧
      selected.rule = rule_lower_2215 ∧ selected.env = cmpEnv cc x y ∧ selected.matched = st ∧
      selected.matchTrace = #[] ∧ ActualRootCalls program ctx cc x y st next #[] selected.rhsTrace out := by
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
  exact ⟨operandType,chosen,envEq,stateEq,traceEq,actual_root_rhs_calls data_program ctx cc x y rhs⟩
/-- Original comparison root selection supplies enough actual fuel for the complete narrow rule split. -/
theorem stock_cmp_narrow_actual_selected_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} {ty : Clif.Ty}
    (half : Bool) (sourceTy : ty = if half then .i16 else .i8) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} {u v : BitVec ty.width} (dfg : DFGCons ctx fr) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ d code,out = .regsVec [[.vreg d .int]] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base code ∧
      ∀ world,Runs F isem (code.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨_,_,_,_,_,calls⟩ := actual_selected_calls inv source clif selected
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ := calls
  have outputDemand := stock_apply_demand_mono outputCall
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  obtain ⟨d,code,result,lower,upper,fragment,execution⟩ := stock_cmp_narrow_actual_emitter_values
    inv half cc sourceTy dfg getX getY typeX typeY enoughEmit enoughCondition
    emitter conditionCall refines bounded extent conditionHeld separatedY
  rw [result] at outputCall
  obtain ⟨output,state⟩ := stock_cmp_output_observed data_program ctx (by omega) outputCall
  rw [state]
  exact ⟨d,code,output,lower,upper,fragment,execution⟩
/-- Original narrow root selection advances the frontier without scratch separation or operand classifications. -/
theorem stock_cmp_narrow_actual_selected_growth {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {cc : Clif.IntCC} {ty : Clif.Ty}
    (half : Bool) (sourceTy : ty = if half then .i16 else .i8) {i x y : Nat} {info : IInfo}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.icmp cc ty x y))
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules)
    {fr : Clif.Frame} {u v : BitVec ty.width} (dfg : DFGCons ctx fr) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    st.base.nextVreg < next.base.nextVreg := by
  obtain ⟨_,_,_,_,_,calls⟩ := actual_selected_calls inv source clif selected
  obtain ⟨emitFuel,conditionFuel,outputFuel,condition,middle,emitTrace,value,produced,conditionTrace,
    enoughEmit,enoughCondition,enoughOutput,emitter,conditionCall,outputCall⟩ := calls
  have outputDemand := stock_apply_demand_mono outputCall
  have conditionHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := outputDemand z
    unfold Demanded at needed ⊢
    omega
  have grows := stock_cmp_narrow_actual_emitter_growth inv half cc sourceTy dfg getX getY typeX typeY
    enoughEmit enoughCondition emitter conditionCall refines bounded extent conditionHeld
  have preserve : next.base = produced.base := by
    have hp := data_program
    have hc : ({} : Config).checkOverlap = false := rfl
    obtain ⟨_,_,_,hL,_,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ := cmp_internal_split_first hc hp.t172 term_172_kind rfl
      (by rw [hp.r172]; simp; omega) outputCall
    rw [show next = _ from congrArg Prod.fst stateEq]
    rw [hp.r172] at hL
    isel_rule_cases hL
    all_goals cases hp
    all_goals isel_inv [*,rule_prelude_lower_105,Stock.sem] at hm he
    all_goals isel_destruct <;> subst_vars
    all_goals have regState := value_reg_state ctx _ produced (by assumption)
    all_goals have wrapState := output_state ctx _ _ (by assumption)
    all_goals rw [wrapState,regState]
  simpa only [preserve] using grows
end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.StockFenceRoot
import FV.Backend.Proof.StockFenceInventory
import FV.Backend.Proof.IselCtlRuleIds

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

section Inventory
attribute [local semireducible] Isle.Aarch64.program
private theorem fence_member : rule_lower_2476 ∈ program.rulesOf T.lower.id := by
  rw [show T.lower.id = 686 from rfl,data_program.r686]
  decide +kernel
private theorem fence_data {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) : info.data = .data 152 19 [.data 151 160 []] := by
  have actual := mapped.data i info _ found source
  have expected : instData f .fence = .ok (.data 152 19 [.data 151 160 []]) := rfl
  exact Except.ok.inj (actual.symm.trans expected)
end Inventory

/-- The actual argument match fixes the selected rule's original source format. -/
private theorem selected_nullary_format {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : ruleFmt selected.rule = some 2466 := by
  have member : selected.rule ∈ R.lower := by simpa only [R.lower,show T.lower.id = 686 from rfl,data_program.r686] using selected.rule_mem
  have checked := List.all_eq_true.mp stock_lower_all_formats selected.rule member
  cases fmt : ruleFmt selected.rule with
  | none => simp only [fmt] at checked; cases checked
  | some ft =>
    simp only [fmt,Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨lo,hi⟩ := checked
    have count : (program.rulesOf T.lower.id).length = 517 := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
    have bound := selected.fuelBound
    obtain ⟨n,eqn⟩ : ∃ n,selected.matchFuel = n+1 := ⟨selected.matchFuel-1,by omega⟩
    have matched := selected.matchedRun
    rw [eqn] at matched
    obtain ⟨env,args,ifs⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    cases shape : selected.rule.args with
    | nil => simp [ruleFmt,shape] at fmt
    | cons head tail =>
      have root : rootFmt head = some ft := by simpa only [ruleFmt,shape] using fmt
      rw [shape] at args
      obtain ⟨env',headRun,tailRun⟩ := matchArgs_cons_inv args
      have small : ft-2447 < 36 := by omega
      obtain ⟨term,lookup,kind⟩ := fmtKinds_program (ft-2447) small
      rw [show 2447+(ft-2447)=ft by omega] at lookup
      obtain ⟨actual,fields,present,data⟩ := rootFmt_match_k data_program root lookup kind headRun
      have same := Option.some.inj (present.symm.trans found)
      subst actual
      have decoded := fence_data mapped found source
      have equal : ft-2447 = 19 := (V.data.inj (decoded.symm.trans data)).2.1.symm
      have exactFmt : ft = 2466 := by omega
      exact congrArg some exactFmt

/-- Original source data identifies root1024 inside actual first-match selection. -/
theorem stock_fence_selected {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_2476 := by
  have fmt := selected_nullary_format mapped found source selected
  have member : selected.rule ∈ R.lower := by simpa only [R.lower,show T.lower.id = 686 from rfl,data_program.r686] using selected.rule_mem
  have candidates : selected.rule ∈ R.lower.filter (fun r => ruleFmt r == some 2466) :=
    List.mem_filter.mpr ⟨member,by simp only [fmt,beq_self_eq_true]⟩
  rw [stock_nullary_inventory] at candidates
  have opcode := stock_selected_source_opcode mapped found source (fence_data mapped found source) selected
  simp only [List.mem_cons,List.not_mem_nil,or_false] at candidates
  rcases candidates with h | h | h | h | h | h | h | h
  all_goals rw [h] at opcode ⊢
  · rw [stock_nullary_opcode_facts.1] at opcode; cases opcode
  · rfl
  · rw [stock_nullary_opcode_facts.2.2.1] at opcode; cases opcode
  · rw [stock_nullary_opcode_facts.2.2.2.1] at opcode; cases opcode
  · rw [stock_nullary_opcode_facts.2.2.2.2.1] at opcode; cases opcode
  · rw [stock_nullary_opcode_facts.2.2.2.2.2.1] at opcode; cases opcode
  · rw [stock_nullary_opcode_facts.2.2.2.2.2.2.1] at opcode; cases opcode
  · rw [stock_nullary_opcode_facts.2.2.2.2.2.2.2] at opcode; cases opcode

/-- Matching the fence root has no if-let effects and retains the exact input state. -/
private theorem fence_matched {ctx : Ctx} {st next : State} {env : Isle.Interp.Env V}
    {tr trace : Array RuleId} {i n : Nat}
    (run : (matchRule program (Stock.sem ctx) {} (n+1) rule_lower_2476 [.inst i]).run
      (st,tr) = .ok (some env,next,trace)) : next = st ∧ trace = tr := by
  obtain ⟨e,args,ifs⟩ := matchRule_some_inv run
  cases n with
  | zero => cases ifs
  | succ n =>
    change Except.ok (some e,st,tr) = Except.ok (some env,next,trace) at ifs
    have same := Except.ok.inj ifs
    exact ⟨(congrArg (fun q => q.2.1) same).symm,(congrArg (fun q => q.2.2) same).symm⟩

/-- Every selected source fence produces no results and emits exactly one fence. -/
theorem stock_fence_selected_exact {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) :
    out = .regsVec [] ∧ next = {st with base := st.base.emit .fence} ∧ trace.getLast? = some 1024 := by
  have chosen := stock_fence_selected mapped found source selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have bound := selected.fuelBound
  obtain ⟨n,equal⟩ : ∃ n, selected.matchFuel = n+1 := ⟨selected.matchFuel-1,by omega⟩
  have matching := selected.matchedRun
  rw [chosen,equal] at matching
  have frame := fence_matched matching
  have evaluated := selected.rhsRun
  rw [chosen,frame.1] at evaluated
  have exactRhs := stock_fence_rhs_exact ctx rfl (by decide) evaluated
  exact ⟨exactRhs.1,exactRhs.2,selected.last_rule.trans (by rw [chosen]; rfl)⟩

end Backend.Stock.Proof

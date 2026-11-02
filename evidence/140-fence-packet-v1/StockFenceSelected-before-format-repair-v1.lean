import FV.Backend.Proof.StockFenceRoot
import FV.Backend.Proof.StockRootOpcodeMatch
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
private theorem fence_ids : sourceOpcodeIds 160 = [1024] := by decide +kernel
private theorem fence_member : rule_lower_2476 ∈ program.rulesOf T.lower.id := by
  rw [show T.lower.id = 686 from rfl,data_program.r686]
  decide +kernel
private theorem fence_data {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) : info.data = .data 152 23 [.data 151 160 []] := by
  have actual := mapped.data i info _ found source
  have expected : instData f .fence = .ok (.data 152 23 [.data 151 160 []]) := rfl
  exact Except.ok.inj (actual.symm.trans expected)
end Inventory

/-- Original source data identifies root1024 inside actual first-match selection. -/
theorem stock_fence_selected {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} (found : ctx.insts[i]? = some info)
    (source : info.clif = some .fence) {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_2476 := by
  have member := stock_selected_source_opcode_ids mapped found source (fence_data mapped found source) selected
  rw [fence_ids] at member
  have identity : selected.rule.id = rule_lower_2476.id := List.mem_singleton.mp member
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem fence_member identity

/-- Matching the fence root has no if-let effects and retains the exact input state. -/
private theorem fence_matched {ctx : Ctx} {st next : State} {env : Isle.Interp.Env V}
    {tr trace : Array RuleId} {i n : Nat}
    (run : (matchRule program (Stock.sem ctx) {} (n+1) rule_lower_2476 [.inst i]).run
      (st,tr) = .ok (some env,next,trace)) : next = st ∧ trace = tr := by
  obtain ⟨e,args,ifs⟩ := matchRule_some_inv run
  change .ok (some e,st,tr) = .ok (some env,next,trace) at ifs
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

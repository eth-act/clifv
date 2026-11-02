import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockBmaskRhs
import FV.Backend.Proof.StockRootOpcodeMatch

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl

section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- The original accepted source determines its real opcode and output type;
the operand type is obtained independently by the real matcher. -/
theorem stock_bmask_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.bmask ty x)) :
    eTy ty = true ∧ info.data = .data 152 29 [.data 151 130 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨supported,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  have expected : instData f (.bmask ty x) =
      .ok (.data 152 29 [.data 151 130 [],.value x]) := by
    simp [instData,supported]; rfl
  exact Except.ok.inj (raw.symm.trans expected)
end SourceData

/-- The actual matcher independently binds the output type, original operand
type and source value, without changing the Stock state. -/
theorem stock_bmask_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x wo : Nat} {info : IInfo} {ti : CTy} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int wo))
    (data : info.data = .data 152 29 [.data 151 130 [],.value x])
    (operandType : ctx.valueType? x = some ti) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2052 [.inst i]).run (st,tr) =
      .ok (some (env3 (.ty (.int wo)) (.ty ti) (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have typed := ext_value_type ctx st.base operandType
  cases hp
  isel_eval [*,rule_lower_2052,env3,sem_extract,sem_unData]
  rfl

/-- A successful actual match supplies its operand type and complete canonical
environment internally. No caller-selected input width is assumed. -/
theorem stock_bmask_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {i x wo n : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int wo))
    (data : info.data = .data 152 29 [.data 151 130 [],.value x])
    {st next : State} {tr trace : Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2052 [.inst i]).run (st,tr) =
      .ok (some env,next,trace)) :
    ∃ ti,ctx.valueType? x = some ti ∧ env = env3 (.ty (.int wo)) (.ty ti) (.value x) ∧
      next = st ∧ trace = tr := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  isel_inv [*,rule_lower_2052,env3,sem_extract,sem_unData,ext_value_type_iff] at matched
  isel_destruct
  simp only [source,Option.some.injEq] at *
  subst_vars
  simp only [data,V.data.injEq,List.cons.injEq] at *
  isel_destruct
  subst_vars
  isel_inv_simp [ext_value_type_iff] at *
  isel_destruct
  subst_vars
  try simp only [source,Option.some.injEq] at *
  subst_vars
  try simp only [type,Option.getD_some] at *
  exact ⟨_,by assumption,rfl⟩

private theorem inventory : sourceOpcodeIds 130 = [936] := by decide +kernel

/-- Original opcode matching determines the selected bmask rule, rather than
taking a selected-root certificate from the caller. -/
theorem stock_selected_bmask_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.bmask ty x)) {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_2052 := by
  obtain ⟨_,data,_⟩ := stock_bmask_source_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  simp only [inventory,List.mem_singleton] at member
  have candidate : rule_lower_2052 ∈ program.rulesOf T.lower.id := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate member

/-- Actual selection supplies the independent original input width, guarded
request, mapped operand, result and complete scheduling/emission state. -/
theorem stock_bmask_selected {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.bmask ty x)) {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) :
    ∃ wi, (wi = 8 ∨ wi = 16 ∨ wi = 32 ∨ wi = 64) ∧ ctx.valueType? x = some (.int wi) ∧
      DemandAllowed ctx st x ∧ ∃ r,ctx.valueReg? x = some r ∧
        out = .regsVec [[bmaskResult st.base wi r]] ∧
        next = {st.mark x with base := bmaskBase st.base wi r} := by
  obtain ⟨output,data,type⟩ := stock_bmask_source_data inv source clif
  have chosen := stock_selected_bmask_rule inv source clif selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel=m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨ti,operandType,envEq,stateEq,traceEq⟩ :=
    stock_bmask_match_observed data_program ctx source type data matched
  have accepted := inv.valTyE x ti operandType
  simp only [eCTys,List.mem_cons,List.not_mem_nil,or_false] at accepted
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at rhs
  rcases accepted with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨_,by simp,operandType,?_⟩
    change (evalExpr program (Stock.sem ctx) {} (999579+420) rule_lower_2052.rhs
      (env3 (.ty (.int ty.width)) (.ty (.int _)) (.value x))).run (st,#[]) =
        .ok (some out,next,selected.rhsTrace) at rhs
    exact stock_bmask_rhs_observed data_program ctx rfl (eTy_width output) (by simp) rhs

end Backend.Stock.Proof.ScalarMask

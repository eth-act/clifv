import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockSelectRootCalls
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Source
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted select supplies its scalar result type and actual ternary data. -/
theorem stock_original_select_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c x y : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y)) :
    (ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧
      info.data = .data 152 24 [.data 151 65 [],.values [c,x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨cmp_eTy_widths supported,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  have expected : instData f (.select ty c x y) = .ok (.data 152 24 [.data 151 65 [],.values [c,x,y]]) := by
    simp [instData,valTyOk,supported]; rfl
  exact Except.ok.inj (raw.symm.trans expected)
private theorem inventory : sourceOpcodeIds 65 = [rule_lower_2267.id] := by decide +kernel
end Source
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
/-- Actual original select matching preserves the complete scheduler and trace. -/
theorem stock_original_select_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i w c x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 24 [.data 151 65 [],.values [c,x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_2267 [.inst i]).run (st,tr) =
      .ok (some (originalSelectEnv w c x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  isel_eval [*,originalSelectEnv,rule_lower_2267,sem_extract,sem_unData,ext_value_array_3]
  rfl
/-- Actual successful original select derives its unique selected root,
canonical match and all650/659/output calls internally. -/
theorem stock_original_select_selected_calls {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c x y : Nat} {info : IInfo} {ty : Clif.Ty} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.select ty c x y))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules) :
    selected.rule = rule_lower_2267 ∧ selected.env = originalSelectEnv ty.width c x y ∧
      selected.matched = st ∧ selected.matchTrace = #[] ∧
      OriginalSelectRootCalls program ctx ty.width c x y st next #[] selected.rhsTrace out := by
  obtain ⟨_,data,type⟩ := stock_original_select_source_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory,List.mem_singleton] at member
  have chosen : selected.rule = rule_lower_2267 := eq_of_mem_of_id lower_ids_nodup selected.rule_mem
    (by change rule_lower_2267 ∈ program.rulesOf 686; rw [data_program.r686]; decide +kernel) member
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_original_select_match data_program ctx source type data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  exact ⟨chosen,envEq.symm,stateEq.symm,traceEq.symm,stock_original_select_rhs_calls data_program ctx ty.width c x y rhs⟩
end Backend.Stock.Proof.ScalarSelect

import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockMinMaxRules
import FV.Backend.Proof.StockMinMaxRegisterRuns
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
def minmaxEnv (w x y : Nat) : Isle.Interp.Env V :=
  #[some (.ty (.int w)),some (.value x),some (.value y)]
section Source
attribute [local semireducible] Isle.Aarch64.program
/-- Original accepted min/max data determines the actual scalar opcode and type. -/
theorem stock_minmax_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (unsigned maximum : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y)) :
    (ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64) ∧
      info.data = .data 152 2 [.data 151 (minmaxOpcode unsigned maximum) [],.values [x,y]] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by
    cases unsigned <;> cases maximum <;> simpa [minmaxOperation,Compile.instE,Compile.binaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.binary (minmaxOperation unsigned maximum) ty x y) =
        .ok (.data 152 2 [.data 151 (minmaxOpcode unsigned maximum) [],.values [x,y]]) := by
      cases unsigned <;> cases maximum <;> simp [minmaxOperation,minmaxOpcode,instData,binaryOpcode,supported] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Source
section Inventory
attribute [local semireducible] Isle.Aarch64.program
private theorem inventory (unsigned maximum : Bool) :
    sourceOpcodeIds (minmaxOpcode unsigned maximum) = [(minmaxRule unsigned maximum).id,(minmaxFallback unsigned maximum).id] := by
  cases unsigned <;> cases maximum
  all_goals simp only [minmaxOpcode,minmaxRule,minmaxFallback,Bool.false_eq_true,ite_true,ite_false]
  all_goals decide +kernel
end Inventory
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
/-- Actual min/max root matching derives its canonical original type/operands
and preserves the complete scheduler state and trace. -/
theorem stock_minmax_match {p : Program} (hp : Data p) (ctx : Ctx) (unsigned maximum : Bool)
    {i w x y : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 2 [.data 151 (minmaxOpcode unsigned maximum) [],.values [x,y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (minmaxRule unsigned maximum) [.inst i]).run (st,tr) =
      .ok (some (minmaxEnv w x y),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases unsigned <;> cases maximum
  all_goals cases hp
  all_goals isel_eval [*,minmaxRule,minmaxOpcode,minmaxEnv,rule_lower_1222,rule_lower_1224,rule_lower_1226,rule_lower_1228,
    sem_extract,sem_unData,ext_value_array_2,ext_ty_int]
  all_goals rfl
section Order
attribute [local semireducible] Isle.Aarch64.program
private theorem fallback_order (unsigned maximum : Bool) :
    (program.rulesOf T.lower.id).idxOf (minmaxRule unsigned maximum) <
      (program.rulesOf T.lower.id).idxOf (minmaxFallback unsigned maximum) := by
  cases unsigned <;> cases maximum <;> decide +kernel
end Order
/-- First-match selection derives the scalar min/max root even though the
opcode inventory also contains a later fallback matching the same scalar data. -/
theorem stock_selected_minmax_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (unsigned maximum : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (minmaxOperation unsigned maximum) ty x y))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) : selected.rule = minmaxRule unsigned maximum := by
  obtain ⟨_,data,type⟩ := stock_minmax_source_data inv unsigned maximum source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have scalarMember : minmaxRule unsigned maximum ∈ program.rulesOf T.lower.id := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    cases unsigned <;> cases maximum <;> decide +kernel
  rcases member with scalar | fallback
  · exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem scalarMember scalar
  · have fallbackMember : minmaxFallback unsigned maximum ∈ program.rulesOf T.lower.id := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]
      cases unsigned <;> cases maximum <;> decide +kernel
    have chosen := eq_of_mem_of_id lower_ids_nodup selected.rule_mem fallbackMember fallback
    have before := fallback_order unsigned maximum
    rw [← chosen] at before
    have earlier : minmaxRule unsigned maximum ∈ selected.pre := by
      by_cases present : minmaxRule unsigned maximum ∈ selected.pre
      · exact present
      · have unique := lower_ids_nodup
        change (List.map Rule.id (program.rulesOf T.lower.id)).Nodup at unique
        have order := congrArg (List.map Rule.id) selected.candidates
        simp only [List.map_append,List.map_cons] at order
        rw [order] at unique
        have absent : selected.rule ∉ selected.pre := by
          intro contained
          have disjoint := (List.nodup_append.mp unique).2.2
          exact (disjoint selected.rule.id (List.mem_map.mpr ⟨_,contained,rfl⟩)
            selected.rule.id (List.mem_cons_self ..)) rfl
        rw [selected.candidates,List.idxOf_append,if_neg present,List.idxOf_append,if_neg absent,List.idxOf_cons_self] at before
        omega
    obtain ⟨fuel,bound,after,failed⟩ := selected.rejected _ earlier
    have count : (program.rulesOf T.lower.id).length = 517 := by
      rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
    obtain ⟨n,equal⟩ : ∃ n,fuel=n+2 := ⟨fuel-2,by omega⟩
    rw [equal,stock_minmax_match data_program ctx unsigned maximum source type data st #[] n] at failed
    cases failed
end Backend.Stock.Proof.ScalarSelect

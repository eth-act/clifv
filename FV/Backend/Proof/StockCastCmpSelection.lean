import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockCastCmpMatch

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

section SourceData
attribute [local semireducible] Isle.Aarch64.program
/-- Original mapped source data supplies the fused cast's exact type and opcode. -/
theorem stock_cast_cmp_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i z : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.extend .uextend ty z)) :
    eTy ty = true ∧ info.resTys.head? = some (.int ty.width) ∧
      info.data = .data 152 29 [.data 151 141 [],.value z] := by
  have supported : eTy ty = true := by
    simpa [Compile.instE,Compile.tyE,eTy] using inv.instE i info _ source clif
  have expected : instData f (.extend .uextend ty z) =
      .ok (.data 152 29 [.data 151 141 [],.value z]) := by
    simp only [instData,supported,ite_true]; rfl
  have data := Except.ok.inj ((inv.data i info _ source clif).symm.trans expected)
  obtain ⟨types,result,typed,_⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨supported,?_,data⟩
  rw [typed]
  cases ty <;> simp_all [eTy,CTy.ofClif,Clif.Ty.width]
end SourceData

/-- Actual fused selection identifies the real original comparison definition,
operand environment and unchanged match state. Root equality is internal
dispatcher data, never an additional accepted-program condition. -/
theorem stock_cast_cmp_selected_definition {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {i z : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.extend .uextend ty z))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) (chosen : selected.rule = rule_lower_1281) :
    ∃ j cmp cc cmpTy x y,ctx.defInst? z = some j ∧ ctx.insts[j]? = some cmp ∧
      cmp.clif = some (.icmp cc cmpTy x y) ∧ selected.env = cmpEnv cc x y ∧
      selected.matched = st ∧ selected.matchTrace = #[] := by
  obtain ⟨_,type,data⟩ := stock_cast_cmp_source_data inv source clif
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨n,fuelEq⟩ : ∃ n,selected.matchFuel = n+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨j,cmp,x,y,cond,operandWidth,defined,found,raw,_,envEq,stateEq,traceEq⟩ :=
    stock_cast_cmp_match_observed data_program ctx source type data matched
  obtain ⟨original,originalEq⟩ := Option.isSome_iff_exists.mp (inv.defClif z j cmp defined found)
  have originalData := inv.data j cmp original found originalEq
  rw [raw] at originalData
  obtain ⟨cc,cmpTy,a,b,instEq,valuesEq,condEq⟩ := instData_icmp_inv originalData
  have pair : x = a ∧ y = b := by simpa only [V.values.injEq,List.cons.injEq,and_true] using valuesEq
  obtain ⟨rfl,rfl⟩ := pair
  subst original
  rw [condEq] at envEq
  exact ⟨j,cmp,cc,cmpTy,_,_,defined,found,originalEq,envEq,stateEq,traceEq⟩

end Backend.Stock.Proof.ScalarCmp

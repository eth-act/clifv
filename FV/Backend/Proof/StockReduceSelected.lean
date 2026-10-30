import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockReduceReceipts
namespace Backend.Stock.Proof.ScalarCast.Reduce
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.ireduce ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 131 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.ireduce ty x) = .ok (.data 152 29 [.data 151 131 [],.value x]) := by
      simp only [instData,supported,ite_true]; rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- Actual reduction selection derives its mapped source and complete
no-allocation/no-emission state; it does not demand a fresh result register. -/
theorem stock_reduce_selected_receipts {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.ireduce ty x))
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rule_lower_2146) :
    ∃ nx,ctx.valueReg? x = some (.vreg nx .int) ∧ out = .regsVec [[.vreg nx .int]] ∧ next = st.mark x := by
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have small : ty.width ≤ 64 := by rcases width with h | h | h | h <;> omega
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_reduce_match data_program ctx source type small data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999959+40) rule_lower_2146.rhs
    (env2 (.ty (.int ty.width)) (.value x))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped⟩ := stock_reduce_rhs_requests data_program ctx rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  rw [stock_reduce_rhs data_program ctx mapped st safe #[] 999959] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  exact ⟨nx,mapped,rhs.1.symm,rhs.2.1.symm⟩
end Backend.Stock.Proof.ScalarCast.Reduce

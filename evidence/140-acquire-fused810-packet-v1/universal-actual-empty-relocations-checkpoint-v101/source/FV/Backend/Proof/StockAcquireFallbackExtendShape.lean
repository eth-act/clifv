import FV.Backend.Proof.StockAcquireConcreteExtendPrefix
import FV.Backend.Proof.StockCastBaseValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

section SourceData
attribute [local semireducible] Isle.Aarch64.program

set_option maxRecDepth 20000 in
/-- Actual mapped source data fixes both original extension operands without source evaluation. -/
theorem fallback_extend_source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[i]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x)) :
    target.width ≤ 64 ∧
      info.data = .data 152 29 [.data 151 (ScalarCast.extendOpcode signed) [],.value x] ∧
      info.resTys.head? = some (.int target.width) := by
  have accepted := inv.instE i info _ installed source
  have supported : eTy target = true := by
    simpa [ScalarCast.extendOp,Compile.instE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ installed source
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ installed source
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,?_⟩
  · cases target <;> simp [eTy,Clif.Ty.width] at supported ⊢
  · have expected : instData f (.extend (ScalarCast.extendOp signed) target x) =
        .ok (.data 152 29 [.data 151 (ScalarCast.extendOpcode signed) [],.value x]) := by
      cases signed <;> simp only [ScalarCast.extendOp,ScalarCast.extendOpcode,instData,supported,ite_true] <;> rfl
    exact Except.ok.inj (raw.symm.trans expected)
  · rw [typed]
    simp [ofClif_int_width (isInt_of_eTy supported)]

end SourceData

/-- Actual selected fallback execution derives the complete emitted extension from compiler types.
The theorem does not assume that the original source extension succeeds or widens. -/
theorem fallback_extend_selected_shape {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[i]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) (chosen : selected.rule = ScalarCast.extendRule signed) :
    ∃ (sourceType : CTy) (pointer : Nat),ctx.valueType? x = some sourceType ∧ sourceType ∈ eCTys ∧
      ctx.valueReg? x = some (.vreg pointer .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.extend (.vreg st.base.nextVreg .int) (.vreg pointer .int) signed sourceType.bits target.width)} := by
  obtain ⟨small,data,type⟩ := fallback_extend_source_data inv signed installed source
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    decide +kernel
  have enough := selected.fuelBound
  rw [count] at enough
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  cases typed : ctx.valueType? x with
  | none =>
    exact False.elim (ScalarCast.stock_extend_match_no_type data_program ctx signed installed type data typed
      st selected.matched #[] selected.matchTrace m selected.env matched)
  | some sourceType =>
    rw [ScalarCast.stock_extend_match data_program ctx signed installed type data typed st #[] m,if_pos small] at matched
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
    obtain ⟨envEq,stateEq,traceEq⟩ := matched
    have rhs := selected.rhsRun
    rw [chosen,← envEq,← stateEq,← traceEq] at rhs
    change (evalExpr program (Stock.sem ctx) {} (999959+40) (ScalarCast.extendRule signed).rhs
      (envExt target.width x sourceType)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
    obtain ⟨safe,rx,mapped⟩ := ScalarCast.stock_extend_rhs_requests data_program ctx signed rhs
    obtain ⟨pointer,rfl⟩ := inv.valueReg x rx mapped
    obtain ⟨trace,forward⟩ := ScalarCast.stock_extend_rhs data_program ctx signed mapped st safe #[] 999959
      (w := target.width) (t := sourceType)
    rw [forward] at rhs
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
    obtain ⟨outEq,stateEq,traceEq⟩ := rhs
    exact ⟨sourceType,pointer,rfl,inv.valTyE x sourceType typed,mapped,outEq.symm,stateEq.symm⟩

end Backend.Stock.Proof.Acquire810

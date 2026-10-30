import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockNegRhs
import FV.Backend.Proof.StockNegSemantics
namespace Backend.Stock.Proof.Neg
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .ineg ty x)) :
    IW ty.width ∧ info.data = .data 152 29 [.data 151 75 [],.value x] ∧
      info.resTys.head? = some (.int ty.width) := by
  have accepted := inv.instE i info _ source clif
  have supported : eTy ty = true := by simpa [Compile.instE,Compile.unaryTyE,Compile.unaryE,Compile.tyE,eTy] using accepted
  have raw := inv.data i info _ source clif
  obtain ⟨types,result,typed,len⟩ := inv.resTys i info _ source clif
  simp only [Clif.Inst.resultTypes] at result
  cases result
  refine ⟨?_,?_,by rw [typed]; simp [ofClif_int_width (isInt_of_eTy supported)]⟩
  · cases ty <;> simp [eTy,Clif.Ty.width,IW] at supported ⊢
  · have expected : instData f (.unary .ineg ty x) = .ok (.data 152 29 [.data 151 75 [],.value x]) := by
      simp only [instData,unaryOpcode,supported,ite_true]; rfl
    exact Except.ok.inj (raw.symm.trans expected)
end Data
/-- Actual scalar negation selection derives its width/environment, guarded
mapped request, full state and final-alias execution value internally. -/
theorem stock_neg_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.unary .ineg ty x))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {u : BitVec ty.width} (get : fr.getAs x ty = .ok u)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = rule_lower_857) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (ρ' : Nat → CV),ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf ty.width) (.vreg st.base.nextVreg .int) .xzr (.vreg nx .int))} ∧
      PRun F isem [(MInst.aluRRR .sub (szOf ty.width) (.vreg st.base.nextVreg .int) .xzr (.vreg nx .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .ineg u⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := source_data inv source clif
  have small : ty.width ≤ 64 := by rcases width with h | h | h | h <;> omega
  have enough := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+2 := ⟨selected.matchFuel-2,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq,stock_neg_match data_program ctx source type small data st #[] m] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [chosen,← envEq,← stateEq,← traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999959+40) rule_lower_857.rhs
    (env2 (.ty (.int ty.width)) (.value x))).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped⟩ := stock_neg_rhs_requests data_program ctx rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapped
  obtain ⟨trace,forward⟩ := stock_neg_rhs data_program ctx small mapped st safe #[] 999959
  rw [forward] at rhs
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at rhs
  obtain ⟨outEq,nextEq,traceEq⟩ := rhs
  have inputHeld : ValuesHeld (fun z => z = x) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro z same; subst z
    rw [← nextEq,Demanded]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]
    omega
  obtain ⟨ρ',execution,value,kept⟩ := stock_neg_resolved refines small bounded mapped inputHeld get
  exact ⟨nx,ρ',mapped,outEq.symm,nextEq.symm,execution,value,kept⟩
end Backend.Stock.Proof.Neg

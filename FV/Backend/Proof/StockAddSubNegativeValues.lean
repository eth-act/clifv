import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockAddSubSemantics
import FV.Backend.Proof.StockAddSubObserved
import FV.Backend.Proof.StockAddSubNegativeMatch
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- The actual selected negative immediate roots compute original add/subtract
values; matching derives the literal and execution derives the guarded request. -/
theorem stock_addsub_neg_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (subtract left : Bool) (side : subtract = true → left = false) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = negImmRule subtract left) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx : Nat) (imm : Imm12) (ρ' : Nat → CV),
      ctx.valueReg? (if left then y else x) = some (.vreg nx .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark (if left then y else x) with base := ((st.base.fresh .int).2.emit
        (.aluRRImm12 (if subtract then .add else .sub) (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) imm))} ∧
      PRun F isem [(.aluRRImm12 (if subtract then .add else .sub) (szOf ty.width) (.vreg st.base.nextVreg .int)
        (.vreg nx .int) imm : MInst).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := stock_addsub_source_data inv subtract source clif
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+40 := ⟨selected.matchFuel-40,by omega⟩
  have getImm : fr.getAs (if left then x else y) ty = .ok (if left then u else v) := by cases left <;> assumption
  have getPlain : fr.getAs (if left then y else x) ty = .ok (if left then v else u) := by cases left <;> assumption
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨imm,envEq,stateEq,traceEq,immBound,immediate⟩ := stock_addsub_neg_match_receipts data_program inv subtract left side
    source clif dfg getImm matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq,traceEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999949+50) (negImmRule subtract left).rhs
    (negImmEnv left ty.width (if left then y else x) (if left then x else y) imm)).run (st,(#[] : Array RuleId).push rule_inst_2404.id) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safe,rx,mapped,outEq,stateEq⟩ := stock_addsub_neg_imm_observed data_program ctx subtract left side width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg _ rx mapped
  have inputs : ValuesHeld (fun k => k = (if left then y else x)) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro k same; subst k
    rw [stateEq]
    unfold Demanded
    change (st.mark (if left then y else x)).demand[if left then y else x]! ≠ 0
    rw [(mark_demand st _ (extent _ _ mapped)).1]; omega
  obtain ⟨ρ',execution,result,kept⟩ := stock_addsub_imm_resolved refines (!subtract) width bounded mapped inputs getPlain immBound immediate
  have original : Clif.Sem.binary (if !subtract then .isub else .iadd) (if left then v else u) (-(if left then u else v)) =
      Clif.Sem.binary (if subtract then .isub else .iadd) u v := by
    cases subtract <;> cases left
    all_goals simp [Clif.Sem.binary,Clif.Sem.iadd,Clif.Sem.isub,BitVec.sub_eq_add_neg,BitVec.neg_neg,BitVec.add_comm]
    cases side rfl
  rw [original] at result
  cases subtract <;> exact ⟨nx,imm,ρ',mapped,outEq,stateEq,execution,result,kept⟩
end Backend.Stock.Proof.ScalarAddSub

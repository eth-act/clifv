import FV.Backend.Proof.StockAddSubValues
import FV.Backend.Proof.StockAddSubImmediateValues
import FV.Backend.Proof.StockAddSubNegativeValues
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
inductive Form where
  | immediate | negative | shifted | extended
  deriving DecidableEq
def Form.rule (form : Form) (subtract left : Bool) : Rule :=
  match form with
  | .immediate => immRule subtract left
  | .negative => negImmRule subtract left
  | .shifted => shiftRule subtract left
  | .extended => extendRule subtract left
/-- Uniform actual-selection value contract for all twelve newly covered
fused add/subtract forms; old base and multiply variants retain their contracts. -/
theorem stock_addsub_fused_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (form : Form) (subtract left : Bool) (side : subtract = true → left = false) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = form.rule subtract left) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV),out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  cases form with
  | immediate =>
    obtain ⟨nx,operand,ρ',mapped,output,state,execution,value,kept⟩ :=
      stock_addsub_imm_selected_values inv subtract left side source clif refines dfg getX getY selected chosen bounded extent held
    refine ⟨.aluRRImm12 (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) operand,ρ',output,?_,execution,value,kept⟩
    rw [state]
  | negative =>
    obtain ⟨nx,operand,ρ',mapped,output,state,execution,value,kept⟩ :=
      stock_addsub_neg_selected_values inv subtract left side source clif refines dfg getX getY selected chosen bounded extent held
    refine ⟨.aluRRImm12 (if subtract then .add else .sub) (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) operand,ρ',output,?_,execution,value,kept⟩
    rw [state]
  | shifted =>
    obtain ⟨z,nx,nz,operand,ρ',mapX,mapZ,output,state,execution,value,kept⟩ :=
      stock_addsub_shift_selected_values inv subtract left side source clif refines dfg getX getY selected chosen bounded extent held
    refine ⟨.aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg nz .int) operand,ρ',output,?_,execution,value,kept⟩
    rw [state]
  | extended =>
    obtain ⟨z,nx,nz,operand,ρ',mapX,mapZ,output,state,execution,value,kept⟩ :=
      stock_addsub_extend_selected_values inv subtract left side source clif refines dfg getX getY selected chosen bounded extent held
    refine ⟨.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg nz .int) operand,ρ',output,?_,execution,value,kept⟩
    rw [state]
end Backend.Stock.Proof.ScalarAddSub

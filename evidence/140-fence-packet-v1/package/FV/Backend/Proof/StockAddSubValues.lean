import FV.Backend.Proof.StockSelectionReceipts
import FV.Backend.Proof.StockAddSubSemantics
import FV.Backend.Proof.StockAddSubObserved
import FV.Backend.Proof.StockAddSubMatch
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem marked_pair (st : State) (x z : Nat) (bx : x < st.demand.size) (bz : z < st.demand.size) :
    Demanded ((st.mark x).mark z) x ∧ Demanded ((st.mark x).mark z) z := by
  have zBound : z < (st.mark x).demand.size := by simpa only [(mark_demand st x bx).2.2] using bz
  constructor
  · unfold Demanded
    by_cases same : x = z
    · subst z; rw [(mark_demand (st.mark x) x (by simpa only [(mark_demand st x bx).2.2] using bx)).1]; omega
    · rw [mark_other (st.mark x) z x same,(mark_demand st x bx).1]; omega
  · unfold Demanded; rw [(mark_demand (st.mark x) z zBound).1]; omega
/-- Selected extended add/subtract executes the original source binary value.
Canonical matching, request guards, fresh writes and allocation are derived
from the actual selection, including fused sources absent from machine registers. -/
theorem stock_addsub_extend_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (subtract left : Bool) (side : subtract = true → left = false) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = extendRule subtract left) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (z nx nz : Nat) (e : ExtendOp) (ρ' : Nat → CV),
      ctx.valueReg? (if left then y else x) = some (.vreg nx .int) ∧ ctx.valueReg? z = some (.vreg nz .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {(st.mark (if left then y else x)).mark z with base := ((st.base.fresh .int).2.emit
        (.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int)
          (.vreg nx .int) (.vreg nz .int) e))} ∧
      PRun F isem [(.aluRRRExtend (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int)
          (.vreg nx .int) (.vreg nz .int) e : MInst).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := stock_addsub_source_data inv subtract source clif
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have getExt : fr.getAs (if left then x else y) ty = .ok (if left then u else v) := by cases left <;> assumption
  have getPlain : fr.getAs (if left then y else x) ty = .ok (if left then v else u) := by cases left <;> assumption
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨cop,ty',z,b,e,a,defined,typed,extended,getZ,sourceWidth,value,envEq,stateEq⟩ :=
    stock_addsub_extend_match_receipts data_program ctx subtract left side source type width data dfg getExt matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999929+70) (extendRule subtract left).rhs
    (extendEnv left ty.width (if left then y else x) z e)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safeX,safeZ,rx,rz,mapX,mapZ,outEq,stateEq⟩ := stock_addsub_extend_observed data_program ctx subtract left side width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg _ rx mapX
  obtain ⟨nz,rfl⟩ := inv.valueReg _ rz mapZ
  have needed := marked_pair st (if left then y else x) z (extent _ _ mapX) (extent _ _ mapZ)
  have inputs : ValuesHeld (fun k => k = (if left then y else x) ∨ k = z) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro k member
    rw [stateEq]
    rcases member with rfl | rfl
    · exact needed.1
    · exact needed.2
  obtain ⟨ρ',execution,result,kept⟩ := stock_addsub_extend_resolved refines subtract width bounded mapX mapZ inputs
    getPlain getZ extended sourceWidth
  have original : Clif.Sem.binary (if subtract then .isub else .iadd) (if left then v else u) (extVal cop ty.width a.bits) =
      Clif.Sem.binary (if subtract then .isub else .iadd) u v := by
    rw [← value]
    cases subtract <;> cases left
    all_goals simp [Clif.Sem.binary,Clif.Sem.iadd,Clif.Sem.isub,BitVec.add_comm]
    cases side rfl
  rw [original] at result
  exact ⟨z,nx,nz,e,ρ',mapX,mapZ,outEq,stateEq,execution,result,kept⟩
theorem stock_addsub_shift_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (subtract left : Bool) (side : subtract = true → left = false) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId} (selected : LowerSelection ctx i st out next rules)
    (chosen : selected.rule = shiftRule subtract left) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (z nx nz : Nat) (sh : ShiftOpAndAmt) (ρ' : Nat → CV),
      ctx.valueReg? (if left then y else x) = some (.vreg nx .int) ∧ ctx.valueReg? z = some (.vreg nz .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {(st.mark (if left then y else x)).mark z with base := ((st.base.fresh .int).2.emit
        (.aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int)
          (.vreg nx .int) (.vreg nz .int) sh))} ∧
      PRun F isem [(.aluRRRShift (if subtract then .sub else .add) (szOf ty.width) (.vreg st.base.nextVreg .int)
          (.vreg nx .int) (.vreg nz .int) sh : MInst).mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if subtract then .isub else .iadd) u v⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  obtain ⟨width,data,type⟩ := stock_addsub_source_data inv subtract source clif
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; rfl
  have enough := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have getExt : fr.getAs (if left then x else y) ty = .ok (if left then u else v) := by cases left <;> assumption
  have getPlain : fr.getAs (if left then y else x) ty = .ok (if left then v else u) := by cases left <;> assumption
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨z,kk,sh,uz,envEq,stateEq,getZ,lsl,amount,value⟩ :=
    stock_addsub_shift_match_receipts data_program inv subtract left side source type width data dfg getExt matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  change (evalExpr program (Stock.sem ctx) {} (999939+60) (shiftRule subtract left).rhs
    (shiftEnv left ty.width (if left then y else x) z (if left then x else y) kk sh)).run (st,#[]) = .ok (some out,next,selected.rhsTrace) at rhs
  obtain ⟨safeX,safeZ,rx,rz,mapX,mapZ,outEq,stateEq⟩ := stock_addsub_shift_observed data_program ctx subtract left side width rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg _ rx mapX
  obtain ⟨nz,rfl⟩ := inv.valueReg _ rz mapZ
  have needed := marked_pair st (if left then y else x) z (extent _ _ mapX) (extent _ _ mapZ)
  have inputs : ValuesHeld (fun k => k = (if left then y else x) ∨ k = z) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro k member
    rw [stateEq]
    rcases member with rfl | rfl
    · exact needed.1
    · exact needed.2
  obtain ⟨ρ',execution,result,kept⟩ := stock_addsub_shift_resolved refines subtract width bounded mapX mapZ inputs
    getPlain getZ lsl amount
  have original : Clif.Sem.binary (if subtract then .isub else .iadd) (if left then v else u) (uz <<< sh.amt) =
      Clif.Sem.binary (if subtract then .isub else .iadd) u v := by
    rw [← value]
    cases subtract <;> cases left
    all_goals simp [Clif.Sem.binary,Clif.Sem.iadd,Clif.Sem.isub,BitVec.add_comm]
    cases side rfl
  rw [original] at result
  exact ⟨z,nx,nz,sh,ρ',mapX,mapZ,outEq,stateEq,execution,result,kept⟩
end Backend.Stock.Proof.ScalarAddSub

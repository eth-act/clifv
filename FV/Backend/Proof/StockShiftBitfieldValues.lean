import FV.Backend.Proof.StockShiftBitfieldSemantics
import FV.Backend.Proof.StockSelectionReceipts
namespace Backend.Stock.Proof.ShiftBitfield
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarShift
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- Actual fused selection establishes the original right-shift source value
using only the guarded underlying operand and fresh result; all other registers
are preserved for later retained-record composition. -/
theorem stock_bitfield_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (signed : Bool) {i z y : Nat} {ty : Clif.Ty} {info : IInfo}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (fusedKind signed).cop ty z y))
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {v : BitVec ty.width} {amount : Clif.Val}
    (getZ : fr.getAs z ty = .ok v) (getY : fr.regs y = some amount)
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace)
    (chosen : selected.rule = fusedRule signed)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (mi : MInst) (ρ' : Nat → CV),out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next.base = (st.base.fresh .int).2.emit mi ∧
      PRun F isem [mi.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      VHolds ⟨ty,(fusedKind signed).value v amount⟩ (ρ' st.base.nextVreg) ∧
      ∀ n,n ≠ st.base.nextVreg → ρ' n = ρ n := by
  have fuelBound := selected.fuelBound
  have count : (program.rulesOf T.lower.id).length ≤ 999987 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]; decide +kernel
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+10 := ⟨selected.matchFuel-10,by omega⟩
  have matched := selected.matchedRun
  rw [chosen,fuelEq] at matched
  obtain ⟨width,x,a,b,u,envEq,stateEq,normA,normB,getX,value⟩ :=
    stock_bitfield_match_receipts data_program inv signed source clif dfg getZ getY matched
  have rhs := selected.rhsRun
  rw [chosen,envEq,stateEq] at rhs
  obtain ⟨safe,r,mapped,output,whole⟩ := stock_bitfield_rhs_observed data_program ctx signed
    (by omega : ty.width ≤ 64) (n := 999959) rhs
  obtain ⟨nx,rfl⟩ := inv.valueReg x r mapped
  have needed : Demanded next x := by
    rw [whole]
    change (st.mark x).demand[x]! ≠ 0
    rw [(mark_demand st x (extent x _ mapped)).1]
    omega
  have heldX := held.read needed (getAs_ok getX) mapped
  obtain ⟨ρ',execution,result,kept⟩ := stock_bitfield_resolved refines signed width
    (a := (a : Int)) (b := (b : Int)) (x := nx) bounded
  refine ⟨fusedCode signed ty.width (.vreg st.base.nextVreg .int) (.vreg nx .int) a b,
    ρ',output,congrArg State.base whole,execution,?_,kept⟩
  change (ρ' st.base.nextVreg).setWidth ty.width = (fusedKind signed).value v amount
  rw [result,normA,normB,heldX,value]
end Backend.Stock.Proof.ShiftBitfield

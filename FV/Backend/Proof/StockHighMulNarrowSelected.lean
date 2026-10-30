import FV.Backend.Proof.StockHighMulNarrowSemantics
import FV.Backend.Proof.StockHighMulSelected
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Narrow selected execution computes the original high product; the technical
non-capture premise is supplied internally by the actual retained-record layer. -/
theorem stock_highmul_narrow_selected_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty x y))
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} (typed : FrameTyped ctx fr) {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ x r,ctx.valueReg? x = some r → x < st.demand.size)
    (secondFree : ∀ ny,ctx.valueReg? y = some (.vreg ny .int) → aliasNum aliases ny ≠ st.base.nextVreg)
    (held : ValuesHeld (Demanded next) ctx fr (fun k => ρ (aliasNum aliases k))) :
    ∃ (nx ny : Nat) (ρ' : Nat → CV),
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regsVec [[.vreg (st.base.nextVreg+3) .int]] ∧
      next = {(st.mark x).mark y with base := narrowBase st.base signed ty.width (.vreg nx .int) (.vreg ny .int)} ∧
      PRun F isem ((narrowCode signed ty.width st.base.nextVreg nx ny).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' (st.base.nextVreg+3)) ∧
      ∀ n,n < st.base.nextVreg ∨ st.base.nextVreg+4 ≤ n → ρ' n = ρ n := by
  have small : ty.width ≤ 32 := by rcases width with h | h | h <;> omega
  obtain ⟨_,_,rx,ry,mapX,mapY,outEq,stateEq⟩ := stock_highmul_narrow_selected inv signed source clif small typed getX getY selected
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have inputs : ValuesHeld (fun k => k = x ∨ k = y) ctx fr (fun k => ρ (aliasNum aliases k)) := by
    apply held.mono
    intro k operand
    rw [stateEq,Demanded]
    change ((st.mark x).mark y).demand[k]! ≠ 0
    rcases operand with operand | operand
    · subst k
      by_cases same : x = y
      · subst y
        rw [(mark_demand (st.mark x) x (by simpa only [State.mark,Array.size_modify] using extent x _ mapX)).1]
        omega
      · rw [mark_other (st.mark x) y x same,(mark_demand st x (extent x _ mapX)).1]
        omega
    · subst k
      rw [(mark_demand (st.mark x) y (by simpa only [State.mark,Array.size_modify] using extent y _ mapY)).1]
      omega
  have heldX := inputs.read (Or.inl rfl) (getAs_ok getX) mapX
  have heldY := inputs.read (Or.inr rfl) (getAs_ok getY) mapY
  obtain ⟨ρ',execution,value,kept⟩ := stock_highmul_narrow_resolved refines signed width bounded (secondFree ny mapY) heldX heldY
  refine ⟨nx,ny,ρ',mapX,mapY,?_,stateEq,execution,value,kept⟩
  simpa [multiplyBase,extendBase,LState.fresh,LState.emit,Nat.add_assoc] using outEq
end Backend.Stock.Proof.ScalarHighMul

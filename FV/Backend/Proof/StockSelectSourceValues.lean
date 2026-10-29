module

public import FV.Backend.Proof.StockSelectObserved
public import FV.Backend.Proof.StockSelectValues
public import FV.Backend.Proof.StockCmpConditionValues
public import FV.Backend.Proof.StockDemandMono

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual explicit-flags659 selects original source values through final
aliases. Both requests and all output/allocation facts come from the call.
Flag production is an internal emitter obligation to be composed by the root
proof, rather than an additional accepted-program condition. -/
theorem stock_select_flags_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {fuel : Nat} (enough : 279 ≤ fuel) {mi : V} {m : MInst} {condition : Cond}
    (decoded : MInst.ofV mi = some m) (noDefs : vdefs m = [])
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 22 659
      [.ty (.int ty.width),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value x,.value y]
      (st,tr) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {ps : Arm.PState} {b : Bool}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (flags : SetsFlags m (fun key => ρ (aliasNum aliases key)) ps) (truth : condOn condition.bits ps = b) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [m,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) condition] ∧
      ∀ world,Runs F isem ([m,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) condition].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,if b then u else v⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
    stock_select_flags_observed hp ctx rfl enough width condition decoded run
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have requestY := stock_put_in_reg ctx (st.mark x) y (.vreg ny .int) mapY safeY
  have demandY := stock_ctor_demand_mono requestY
  have neededX : Demanded next x := by
    have first := (mark_demand st x (extent x _ mapX)).1
    have second := demandY x
    rw [finish]
    unfold Demanded
    simp only [State.mark] at first second ⊢
    omega
  have extentY : y < (st.mark x).demand.size := by simpa only [State.mark,Array.size_modify] using extent y _ mapY
  have neededY : Demanded next y := by
    have second := (mark_demand (st.mark x) y extentY).1
    rw [finish]
    unfold Demanded
    simp only [State.mark] at second ⊢
    omega
  have inputX := held.read neededX (getAs_ok getX) mapX
  have inputY := held.read neededY (getAs_ok getY) mapY
  refine ⟨nx,ny,st.base.nextVreg,mapX,mapY,output,Nat.le_refl _,?_,?_,?_⟩
  · rw [finish]
    simp [LState.fresh,LState.emit]
  · rw [finish]
    exact Frag.fresh_emit2 st.base noDefs (by
      change vdefs (.csel (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) condition) ⊆ [st.base.nextVreg]
      rw [vdefs_csel]
      exact List.Subset.refl _)
  · intro world
    exact stock_select_flags_resolved refines (by omega) bounded
      (ScalarCmp.stock_cmp_sets_flags_resolved flags) truth inputX inputY world
end Backend.Stock.Proof.ScalarSelect

import FV.Backend.Proof.StockSelectZeroObserved
import FV.Backend.Proof.StockSelectValues
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual Zero/NotZero659 executes its register-zero producer through final aliases
and selects the original source operands, deriving all requests and output state. -/
theorem stock_select_zero_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {ty : Clif.Ty} (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {fuel : Nat} (enough : 319 ≤ fuel) (nonzero : Bool) (size : OperandSize) (key : Nat)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 22 659
      [.ty (.int ty.width),.data 123 (if nonzero then 1 else 0) [.reg (.vreg key .int),.data 93 (if size = .size32 then 0 else 1) []],.value x,.value y]
      (st,tr) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpXzr size key,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (if nonzero then .ne else .eq)] ∧
      ∀ world,Runs F isem ([cmpXzr size key,.csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (if nonzero then .ne else .eq)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,if (if nonzero then opnd size (ρ (aliasNum aliases key)) != 0 else opnd size (ρ (aliasNum aliases key)) == 0) then u else v⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,output,finish⟩ :=
    stock_select_zero_observed hp ctx rfl enough width nonzero size key run
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
    exact Frag.fresh_emit2 st.base rfl (by
      change vdefs (.csel (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) (if nonzero then .ne else .eq)) ⊆ [st.base.nextVreg]
      rw [vdefs_csel]
      exact List.Subset.refl _)
  · intro world
    have flags := setsFlags_cmpXzr size key (fun k => ρ (aliasNum aliases k))
    have truth : condOn (if nonzero then Cond.ne else Cond.eq).bits
        (cmpFlags (opnd size (ρ (aliasNum aliases key))) 0) =
        (if nonzero then opnd size (ρ (aliasNum aliases key)) != 0 else opnd size (ρ (aliasNum aliases key)) == 0) := by
      cases nonzero
      · exact ScalarCmp.stock_cmp_zero_flag _ _
      · exact ScalarCmp.stock_cmp_conditions (n := size.bits) (by cases size <;> simp [OperandSize.bits]) .ne
          (opnd size (ρ (aliasNum aliases key))) 0
    exact stock_select_flags_resolved refines (by omega) bounded
      (ScalarCmp.stock_cmp_sets_flags_resolved flags) truth inputX inputY world
end Backend.Stock.Proof.ScalarSelect

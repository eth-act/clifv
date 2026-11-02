import FV.Backend.Proof.StockCmpNonzero8Emission
import FV.Backend.Proof.StockCmpNonzero8OriginalSelection
import FV.Backend.Proof.StockCmpTestFlags
import FV.Backend.Proof.StockSelectSourceValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
/-- The actual8-bit source condition uses the real masked flags producer and
selects original source operands through final aliases. Condition truth comes
from the original getter, including dirty high machine bits. -/
theorem stock_select_nonzero8_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {c x y : Nat} {test : BitVec 8} {u v : BitVec ty.width}
    (getC : fr.getAs c .i8 = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typed : ctx.valueType? c = some (.int 8))
    {emitFuel selectFuel : Nat} (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (st,tr) condition (middle,emitterTrace))
    {consumerStart : Array RuleId}
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,consumerStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key nx ny d,ctx.valueReg? c = some (.vreg key .int) ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .ne] ∧
      ∀ world,Runs F isem ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .ne].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
            VHolds ⟨ty,if test != 0 then u else v⟩ (final d) ∧ ∀ k,k ≠ d → final k = ρ k) := by
  obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero8_selected ctx inv (by omega) typed emitter
  obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+100 := ⟨emitFuel-100,by omega⟩
  rw [gas] at rhs
  obtain ⟨safeC,rx,mapped,producer,finish⟩ := ScalarCmp.stock_cmp_nonzero8_rhs_observed data_program ctx rfl rhs
  obtain ⟨key,rfl⟩ := inv.valueReg c rx mapped
  have neededC : Demanded next c := by
    have needed := (mark_demand st c (extent c _ mapped)).1
    have grows := stock_apply_demand_mono consumer c
    rw [finish] at grows
    unfold Demanded at needed ⊢
    omega
  have input := held.read neededC (getAs_ok getC) mapped
  have flags := setsFlags_tst255 key (fun k => ρ (aliasNum aliases k))
  have truth := ScalarCmp.stock_cmp_truthy8 test (ρ (aliasNum aliases key)) input
  have middleBound : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  have middleExtent : ∀ value r,ctx.valueReg? value = some r → value < middle.demand.size := by
    intro value r map
    rw [finish]
    simpa only [State.mark,Array.size_modify] using extent value r map
  rw [producer] at consumer
  obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ := stock_select_flags_source_values data_program inv
    width getX getY (by omega) (ofV_tst .xzr (.vreg key .int) ⟨255,.size32⟩) rfl consumer
    refines middleBound middleExtent held flags truth
  rw [finish] at lower fragment
  exact ⟨key,nx,ny,d,mapped,mapX,mapY,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect

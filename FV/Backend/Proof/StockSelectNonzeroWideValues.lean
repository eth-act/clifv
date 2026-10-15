import FV.Backend.Proof.StockSelectNonzeroWideShape
import FV.Backend.Proof.StockSelectZeroSourceValues
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual wide nonzero condition production and actual659 selection compute
original source values, deriving condition truth from the original getter and
real guarded demand. No externally supplied flag or condition-value certificate. -/
theorem stock_select_nonzero_wide_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (wide : Bool) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {c x y : Nat} {test : BitVec (if wide then Clif.Ty.i64 else .i32).width}
    {u v : BitVec ty.width} (getC : fr.getAs c (if wide then .i64 else .i32) = .ok test)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typed : ctx.valueType? c = some (.int (if wide then 64 else 32)))
    {emitFuel selectFuel : Nat} (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (st,tr) condition (middle,emitterTrace))
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,emitterTrace) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key nx ny d,ctx.valueReg? c = some (.vreg key .int) ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpXzr (if wide then .size64 else .size32) key,
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .ne] ∧
      ∀ world,Runs F isem ([cmpXzr (if wide then .size64 else .size32) key,
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) .ne].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
            VHolds ⟨ty,if test != 0 then u else v⟩ (final d) ∧ ∀ k,k ≠ d → final k = ρ k) := by
  obtain ⟨safeC,key,mapC,producer,finish⟩ := stock_select_nonzero_wide_emitter_observed inv wide enoughEmit typed emitter
  have neededC : Demanded next c := by
    have needed := (mark_demand st c (extent c _ mapC)).1
    have grows := stock_apply_demand_mono consumer c
    rw [finish] at grows
    unfold Demanded at needed ⊢
    omega
  have input := held.read neededC (getAs_ok getC) mapC
  have word : (opnd (if wide then .size64 else .size32) (ρ (aliasNum aliases key)) != 0) = (test != 0) := by
    cases wide
    · simp only [Bool.false_eq_true,ite_false,Clif.Ty.width] at input ⊢
      change (ρ (aliasNum aliases key)).setWidth 32 = test at input
      have same : opnd .size32 (ρ (aliasNum aliases key)) = test := by
        change ((ρ (aliasNum aliases key)).setWidth 64).setWidth 32 = test
        rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
        exact input
      change (opnd .size32 (ρ (aliasNum aliases key)) != 0) = (test != 0)
      rw [same]
      rfl
    · simp only [ite_true,Clif.Ty.width] at input ⊢
      change (ρ (aliasNum aliases key)).setWidth 64 = test at input
      have same : opnd .size64 (ρ (aliasNum aliases key)) = test := by
        simpa only [opnd,OperandSize.bits,lo64,BitVec.setWidth_eq] using input
      change (opnd .size64 (ρ (aliasNum aliases key)) != 0) = (test != 0)
      rw [same]
      rfl
  rw [producer] at consumer
  have conditionEq : (if wide then 1 else 0) =
      if (if wide then OperandSize.size64 else .size32) = .size32 then 0 else 1 := by cases wide <;> rfl
  rw [conditionEq] at consumer
  have middleBound : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  have middleExtent : ∀ value r,ctx.valueReg? value = some r → value < middle.demand.size := by
    intro value r mapped
    rw [finish]
    simpa only [State.mark,Array.size_modify] using extent value r mapped
  obtain ⟨nx,ny,d,mapX,mapY,output,lower,upper,fragment,execution⟩ :=
    stock_select_zero_source_values data_program inv width getX getY enoughSelect true
      (if wide then .size64 else .size32) key consumer refines middleBound middleExtent held
  simp only [ite_true,word] at execution fragment
  rw [finish] at lower fragment
  exact ⟨key,nx,ny,d,mapC,mapX,mapY,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarSelect

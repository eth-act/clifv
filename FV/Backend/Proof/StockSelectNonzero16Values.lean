import FV.Backend.Proof.StockCmpNonzero16Values
import FV.Backend.Proof.StockSelectNonzero16Shape
import FV.Backend.Proof.StockSelectZeroObserved
import FV.Backend.Proof.StockSelectZeroReplacementResolved
import FV.Backend.Proof.StockSelectCompanionFragment
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Original16-bit condition production and actual659 select compute source
values after the real extension prefix. Final-source separation is an internal
retained-availability obligation covering the entire two-register allocation. -/
theorem stock_select_nonzero16_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {ty : Clif.Ty}
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {c x y : Nat} {test : BitVec 16} {u v : BitVec ty.width}
    (getC : fr.getAs c .i16 = .ok test) (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typed : ctx.valueType? c = some (.int 16))
    {emitFuel selectFuel : Nat} (enoughEmit : 220 ≤ emitFuel) (enoughSelect : 319 ≤ selectFuel)
    {st middle next : State} {tr emitterTrace trace : Array RuleId} {condition out : V}
    (empty : st.base.emitted = #[])
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 651 [.value c]
      (st,tr) condition (middle,emitterTrace))
    {consumerStart : Array RuleId}
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,consumerStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ value r,ctx.valueReg? value = some r → value < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (outsideX : ∀ key,ctx.valueReg? x = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key)
    (outsideY : ∀ key,ctx.valueReg? y = some (.vreg key .int) →
      aliasNum aliases key < st.base.nextVreg ∨ next.base.nextVreg ≤ aliasNum aliases key) :
    ∃ key nx ny,ctx.valueReg? c = some (.vreg key .int) ∧
      ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg (st.base.nextVreg+1) .int] ∧ next.base.nextVreg = st.base.nextVreg+2 ∧
      Frag st.base next.base [.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32,
        cmpXzr .size32 st.base.nextVreg,
        .csel (.vreg (st.base.nextVreg+1) .int) (.vreg nx .int) (.vreg ny .int) .ne] ∧
      ∀ world,Runs F isem ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32,
        cmpXzr .size32 st.base.nextVreg,
        .csel (.vreg (st.base.nextVreg+1) .int) (.vreg nx .int) (.vreg ny .int) .ne].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
            VHolds ⟨ty,if test != 0 then u else v⟩ (final (st.base.nextVreg+1)) ∧
            ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → final k = ρ k) := by
  obtain ⟨safeC,key,mapC,producer,finish⟩ := stock_select_nonzero16_emitter_observed inv enoughEmit typed emitter
  rw [producer] at consumer
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,output,complete⟩ := stock_select_zero_observed data_program ctx rfl
    enoughSelect width true .size32 st.base.nextVreg consumer
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have middleFrontier : middle.base.nextVreg = st.base.nextVreg+1 := by rw [finish]; rfl
  have finalFrontier : next.base.nextVreg = st.base.nextVreg+2 := by rw [complete]; simp only [LState.fresh,LState.emit,middleFrontier]
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by omega
  have extentMiddle : ∀ value r,ctx.valueReg? value = some r → value < middle.demand.size := by
    intro value r mapped
    rw [finish]
    simpa only [State.mark,Array.size_modify] using extent value r mapped
  have neededX : Demanded next x := by
    have first := (mark_demand middle x (extentMiddle x _ mapX)).1
    have second := stock_ctor_demand_mono (stock_put_in_reg ctx (middle.mark x) y (.vreg ny .int) mapY safeY) x
    rw [complete]
    unfold Demanded
    simp only [State.mark] at first second ⊢
    omega
  have neededY : Demanded next y := by
    have bound : y < (middle.mark x).demand.size := by simpa only [State.mark,Array.size_modify] using extentMiddle y _ mapY
    have last := (mark_demand (middle.mark x) y bound).1
    rw [complete]
    unfold Demanded
    simp only [State.mark] at last ⊢
    omega
  have inputX := held.read neededX (getAs_ok getX) mapX
  have inputY := held.read neededY (getAs_ok getY) mapY
  let ghost := {middle with base := (((middle.base.fresh .int).2.emit (cmpImm0 .size32 st.base.nextVreg)).emit
    (.cset (middle.base.fresh .int).1 .ne))}
  obtain ⟨booleanTrace,booleanCall⟩ := ScalarCmp.stock_cmp_condition_zero data_program ctx (cfg := {}) rfl
    true .size32 middle emitterTrace 0 (.vreg st.base.nextVreg .int)
  have actualBoolean : ApplyInternal program (Stock.sem ctx) {} 119 27 715 [condition]
      (middle,emitterTrace) (.reg (middle.base.fresh .int).1) (ghost,booleanTrace) := by
    rw [producer]
    exact booleanCall
  have ghostHeld : ValuesHeld (Demanded ghost) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro value needed
    have grows := stock_apply_demand_mono consumer value
    change middle.demand[value]! ≠ 0 at needed
    change next.demand[value]! ≠ 0
    omega
  obtain ⟨rhsTrace,rhs,_⟩ := ScalarCmp.stock_cmp_original_nonzero16_selected ctx inv (by omega) typed emitter
  obtain ⟨n,gas⟩ : ∃ n,emitFuel=n+220 := ⟨emitFuel-220,by omega⟩
  rw [gas] at rhs
  obtain ⟨ms,r,d,booleanOutput,lower,upper,fragment,execution⟩ := ScalarCmp.stock_cmp_nonzero16_rhs_source_values
    data_program inv dfg getC (by decide) rhs actualBoolean refines bounded extent ghostHeld
  have equalD : d = st.base.nextVreg+1 := by
    have equal := (Reg.vreg.inj (V.reg.inj booleanOutput)).1.symm
    simpa only [LState.fresh,middleFrontier] using equal
  subst d
  have ghostFrontier : ghost.base.nextVreg = next.base.nextVreg := by
    change middle.base.nextVreg+1 = next.base.nextVreg
    omega
  have code := stock_select_companion_fragment_code empty fragment
  have prefixCode : middle.base.emitted.toList =
      [.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32] := by
    rw [finish]
    simp [LState.fresh,LState.emit,empty]
  simp only [prefixCode,LState.fresh,middleFrontier] at code
  rw [code] at execution fragment
  have first : Frag st.base middle.base [.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32] := by
    rw [finish]
    exact Frag.fresh_emit st.base (by change vdefs (.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32) ⊆ [st.base.nextVreg]; rw [vdefs_extend']; exact List.Subset.refl _)
  have whole : Frag st.base next.base
      [.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32,cmpXzr .size32 st.base.nextVreg,
        .csel (.vreg (st.base.nextVreg+1) .int) (.vreg nx .int) (.vreg ny .int) .ne] := by
    rw [complete]
    have tail := Frag.fresh_emit2 middle.base (m1 := cmpXzr .size32 st.base.nextVreg) rfl
      (m2 := .csel (middle.base.fresh .int).1 (.vreg nx .int) (.vreg ny .int) .ne)
      (by rw [show (middle.base.fresh .int).1 = .vreg middle.base.nextVreg .int from rfl,vdefs_csel]; exact List.Subset.refl _)
    simpa only [LState.fresh,middleFrontier,List.cons_append,List.nil_append,ite_true] using first.append tail
  refine ⟨key,nx,ny,mapC,mapX,mapY,?_,finalFrontier,whole,?_⟩
  · simpa only [LState.fresh,middleFrontier] using output
  · intro world
    apply stock_select_replace_zero_cset_resolved refines true .size32 st.base.nextVreg (by omega)
      (aliases := aliases) (leading := [.extend (.vreg st.base.nextVreg .int) (.vreg key .int) false 16 32])
      (by omega) (by rcases outsideX nx mapX with h | h <;> omega)
      (by rcases outsideY ny mapY with h | h <;> omega) (by intro k h; rcases h with h | h <;> omega)
    apply (execution world).imp
    intro final _ _ pair
    obtain ⟨value,frame⟩ := pair
    rw [ghostFrontier] at frame
    exact ⟨value,by rw [frame _ (outsideX nx mapX)]; exact inputX,
      by rw [frame _ (outsideY ny mapY)]; exact inputY,frame⟩
end Backend.Stock.Proof.ScalarSelect

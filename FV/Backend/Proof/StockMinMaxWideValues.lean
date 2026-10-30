import FV.Backend.Proof.IselCmpMinMax
import FV.Backend.Proof.StockCmpWideActualValues
import FV.Backend.Proof.StockMinMaxWideShape
import FV.Backend.Proof.StockSelectBooleanCompanion
import FV.Backend.Proof.StockSelectReplacementResolved
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Every actual wide minmax emitter/select pair computes its original source
value. Operand classes are derived by the complete comparison proof. Final-source
separation is an internal retained-availability obligation, not an input check. -/
theorem stock_minmax_wide_emitter_source_values {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (unsigned maximum wide : Bool) {ty : Clif.Ty}
    (sourceTy : ty = if wide then .i64 else .i32)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width} (dfg : DFGCons ctx fr)
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32)))
    {st middle next : State} {tr emitTrace trace : Array RuleId} {emitFuel selectFuel : Nat}
    {condition out : V} (enoughEmit : 300 ≤ emitFuel) (enoughSelect : 279 ≤ selectFuel)
    (emitter : ApplyInternal program (Stock.sem ctx) {} emitFuel 123 652
      [.data 145 (ccIdx (minmaxComparison unsigned maximum)) [],.value x,.value y]
      (st,tr) condition (middle,emitTrace))
    (consumer : ApplyInternal program (Stock.sem ctx) {} selectFuel 22 659
      [.ty (.int ty.width),condition,.value x,.value y] (middle,emitTrace) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separateX : ∀ r,ctx.valueReg? x = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg)
    (separateY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ nx ny m,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg st.base.nextVreg .int] ∧ next.base.nextVreg = st.base.nextVreg+1 ∧
      Frag st.base next.base [m,.csel (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int)
        (condOf (minmaxComparison unsigned maximum))] ∧
      ∀ world,Runs F isem ([m,.csel (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int)
        (condOf (minmaxComparison unsigned maximum))].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun final _ => VHolds ⟨ty,Clif.Sem.binary (minmaxOperation unsigned maximum) u v⟩
          (final st.base.nextVreg) ∧ ∀ k,k ≠ st.base.nextVreg → final k = ρ k) := by
  let cc := minmaxComparison unsigned maximum
  have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    rw [sourceTy]; cases wide <;> simp [Clif.Ty.width]
  obtain ⟨mi,conditionEq,baseEq,sizeEq⟩ := stock_minmax_wide_emitter_shape inv unsigned maximum wide
    typeX typeY enoughEmit emitter
  rw [conditionEq] at consumer emitter
  obtain ⟨m,rx,ry,decoded,safeX,safeY,mapX,mapY,output,finish,booleanTrace,booleanCall⟩ :=
    stock_select_flags_boolean_companion data_program ctx rfl enoughSelect width (condOf cc) consumer
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have demand := stock_apply_demand_mono consumer
  have ghostHeld : ValuesHeld (Demanded {middle with base := (((middle.base.fresh .int).2.emit m).emit
      (.cset (middle.base.fresh .int).1 (condOf cc)))}) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := demand z
    change middle.demand[z]! ≠ 0 at needed
    change next.demand[z]! ≠ 0
    omega
  obtain ⟨d,code,booleanOutput,lower,upper,fragment,execution⟩ := stock_cmp_wide_actual_emitter_values
    inv wide cc sourceTy dfg getX getY typeX typeY enoughEmit (by decide) emitter booleanCall
      refines bounded extent ghostHeld
  have equalD : d = st.base.nextVreg := by
    have equal := (Reg.vreg.inj (V.reg.inj booleanOutput)).1.symm
    simpa only [LState.fresh,baseEq] using equal
  subst d
  have codeEq : code = [m,.cset (.vreg st.base.nextVreg .int) (condOf cc)] := by
    have emitted := congrArg Array.toList fragment.emitted
    apply List.append_cancel_left (as := st.base.emitted.toList)
    simpa only [LState.emit,LState.fresh,baseEq,Array.toList_push,Array.toList_append,List.toList_toArray,
      List.append_assoc,List.cons_append,List.nil_append] using emitted.symm
  rw [codeEq] at execution fragment
  rw [baseEq] at fragment
  have extentMiddle : ∀ z r,ctx.valueReg? z = some r → z < middle.demand.size := by
    intro z r mapped
    rw [sizeEq]
    exact extent z r mapped
  have neededX : Demanded next x := by
    have first := (mark_demand middle x (extentMiddle x _ mapX)).1
    have request := stock_ctor_demand_mono (stock_put_in_reg ctx (middle.mark x) y (.vreg ny .int) mapY safeY)
    have second := request x
    rw [finish]
    unfold Demanded
    simp only [State.mark] at first second ⊢
    omega
  have neededY : Demanded next y := by
    have bound : y < (middle.mark x).demand.size := by
      simpa only [State.mark,Array.size_modify] using extentMiddle y _ mapY
    have marked := (mark_demand (middle.mark x) y bound).1
    rw [finish]
    unfold Demanded
    simp only [State.mark] at marked ⊢
    omega
  have inputX := held.read neededX (getAs_ok getX) mapX
  have inputY := held.read neededY (getAs_ok getY) mapY
  have actualNext : next.base = (((st.base.fresh .int).2.emit m).emit
      (.csel (.vreg st.base.nextVreg .int) (.vreg nx .int) (.vreg ny .int) (condOf cc))) := by
    rw [finish,baseEq]; rfl
  refine ⟨nx,ny,m,mapX,mapY,?_,?_,?_,?_⟩
  · simpa only [baseEq,LState.fresh] using output
  · rw [actualNext]; simp [LState.fresh,LState.emit]
  · rw [actualNext]
    refine ⟨?_,fragment.mono,?_⟩
    · apply Array.toList_inj.mp; simp [LState.fresh,LState.emit,cc]
    · intro inst member k defined
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact fragment.defs inst (by simp) k defined
      · apply fragment.defs (.cset (.vreg st.base.nextVreg .int) (condOf cc)) (by simp) k
        simpa only [vdefs_csel,vdefs_cset] using defined
  · intro world
    have comparison : Runs F isem
        ([m,MInst.cset (.vreg st.base.nextVreg .int) (condOf cc)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world
        (fun regs _ => VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (regs st.base.nextVreg) ∧
          VHolds ⟨ty,u⟩ (regs (aliasNum aliases nx)) ∧ VHolds ⟨ty,v⟩ (regs (aliasNum aliases ny)) ∧
          ∀ k,k ≠ st.base.nextVreg → regs k = ρ k) :=
      (execution world).imp (fun regs _ _ post =>
      ⟨post.1,(by rw [post.2 (aliasNum aliases nx) (by have := separateX nx mapX; simp only [LState.fresh,LState.emit,baseEq]; omega)]; exact inputX),
        (by rw [post.2 (aliasNum aliases ny) (by have := separateY ny mapY; simp only [LState.fresh,LState.emit,baseEq]; omega)]; exact inputY),
        fun k different => post.2 k (by simp only [LState.fresh,LState.emit,baseEq]; omega)⟩)
    have selected := stock_select_replace_cset_resolved refines (condOf_ne_al cc)
      (by rw [sourceTy]; cases wide <;> decide) bounded (separateX nx mapX) (separateY ny mapY)
      (fun k h => h) (leading := [m]) comparison
    apply selected.imp
    intro regs _ _ post
    refine ⟨?_,post.2⟩
    have semantics : (if Clif.Sem.intcc cc u v then u else v) =
        Clif.Sem.binary (minmaxOperation unsigned maximum) u v := by
      cases unsigned <;> cases maximum
      · exact (minmax_sem ty.width u v).2.1
      · exact (minmax_sem ty.width u v).2.2.2
      · exact (minmax_sem ty.width u v).1
      · exact (minmax_sem ty.width u v).2.2.1
    simpa only [semantics] using post.1
end Backend.Stock.Proof.ScalarSelect

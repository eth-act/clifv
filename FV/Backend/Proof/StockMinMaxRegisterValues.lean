import FV.Backend.Proof.IselCmpDivRoot
import FV.Backend.Proof.StockCmpRegisterEmission
import FV.Backend.Proof.StockSelectSourceValues
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
private theorem operand_of_value {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {u : BitVec ty.width} {A : CV} (sg : Bool) (held : VHolds ⟨ty,u⟩ A) : DivOpnd sg u A := by
  cases ty <;> simp only [Clif.Ty.width] at width
  all_goals try (omega)
  all_goals first
    | exact divOpnd_of_vholds64 rfl held
    | change BitVec 32 at u
      change A.setWidth 32 = u at held
      have signed : u.signExtend 32 = u := BitVec.signExtend_eq u
      have unsigned : u.setWidth 32 = u := BitVec.setWidth_eq u
      change (lo64 A).setWidth 32 = (if sg then u.signExtend 32 else u.setWidth 32)
      rw [signed,unsigned,ite_self]
      change (A.setWidth 64).setWidth 32 = u
      rw [BitVec.setWidth_setWidth_of_le A (by decide)]
      exact held
/-- Actual register-emitter flags and659 selection compose into the selected
original32/64 source value through final aliases. Producer flag semantics,
requests, allocation and the outside-result register frame are derived. The
selected minmax roots and other emitter forms must still compose this helper. -/
theorem stock_select_register_emitter_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (cc : Clif.IntCC)
    {ty : Clif.Ty} (width : ty.width = 32 ∨ ty.width = 64)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    {st middle next : State} {tr emitTrace trace : Array RuleId} {n fuel : Nat} {condition out : V}
    (enough : 279 ≤ fuel)
    (emitter : (evalExpr p (Stock.sem ctx) {} (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (szOf ty.width).bits)),some (.value y)]).run
      (st,tr) = .ok (some condition,middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 22 659 [.ty (.int ty.width),condition,.value x,.value y]
      (middle,emitTrace) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .regs [.vreg d .int] ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int),
        .csel (.vreg d .int) (.vreg nx .int) (.vreg ny .int) (condOf cc)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨ty,if Clif.Sem.intcc cc u v then u else v⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,producer,finish⟩ := stock_cmp_register_rhs_observed hp ctx rfl cc (szOf ty.width) emitter
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have conditionDemand := stock_apply_demand_mono conditionCall
  have requestY := stock_put_in_reg ctx (st.mark x) y (.vreg ny .int) mapY safeY
  have requestDemand := stock_ctor_demand_mono requestY
  have neededX : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapX)).1
    have after := requestDemand x
    have done := conditionDemand x
    rw [finish] at done
    unfold Demanded
    omega
  have extentY : y < (st.mark x).demand.size := by simpa only [State.mark,Array.size_modify] using extent y _ mapY
  have neededY : Demanded next y := by
    have marked := (mark_demand (st.mark x) y extentY).1
    have done := conditionDemand y
    rw [finish] at done
    unfold Demanded
    omega
  have inputX := operand_of_value width (signedCC cc) (held.read neededX (getAs_ok getX) mapX)
  have inputY := operand_of_value width (signedCC cc) (held.read neededY (getAs_ok getY) mapY)
  have allWidth : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by omega
  have truth := stock_cmp_original_flags allWidth cc inputX inputY
  have flags := setsFlags_cmpRR (szOf ty.width) nx ny (fun key => ρ (aliasNum aliases key))
  rw [producer] at conditionCall
  have decoded : MInst.ofV (.data 58 2 [.data 59 10 [],
      .data 93 (if szOf ty.width = .size32 then 0 else 1) [],.reg .xzr,.reg (.vreg nx .int),.reg (.vreg ny .int)]) =
      some (.aluRRR .subS (szOf ty.width) .xzr (.vreg nx .int) (.vreg ny .int)) := by
    cases szOf ty.width <;> rfl
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  have extentMiddle : ∀ z r,ctx.valueReg? z = some r → z < middle.demand.size := by
    intro z r mapped
    rw [finish]
    simpa only [State.mark,Array.size_modify] using extent z r mapped
  obtain ⟨nx',ny',d,mapX',mapY',output,lower,upper,fragment,execution⟩ :=
    stock_select_flags_source_values hp inv allWidth getX getY enough decoded rfl conditionCall refines
      boundedMiddle extentMiddle held flags truth
  have sameX : nx' = nx := (Reg.vreg.inj (Option.some.inj (mapX'.symm.trans mapX))).1
  have sameY : ny' = ny := (Reg.vreg.inj (Option.some.inj (mapY'.symm.trans mapY))).1
  subst nx'
  subst ny'
  refine ⟨nx,ny,d,mapX,mapY,output,?_,upper,?_,execution⟩
  · rw [finish] at lower
    exact lower
  · rw [finish] at fragment
    exact fragment

end Backend.Stock.Proof.ScalarSelect

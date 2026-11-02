import FV.Backend.Proof.StockExtendSemantics
import FV.Backend.Proof.StockCmpNarrowRhsObserved
import FV.Backend.Proof.StockDemandMono
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockCmpNarrowFlags
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual narrow emitter-RHS and condition executions compute the original
source predicate through final aliases. Right-source separation is an internal
fragment obligation discharged from original availability at retained records. -/
theorem stock_cmp_narrow_condition_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (half : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    {fr : Clif.Frame} {x y : Nat} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enough : 119 ≤ fuel)
    (emitter : (evalExpr p (Stock.sem ctx) {} (n+160)
      (if signedCC cc then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),
        some (.ty (.int (if half then 16 else 8))),some (.value y)]).run (st,tr) =
      .ok (some condition,middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key)))
    (separatedY : ∀ r,ctx.valueReg? y = some (.vreg r .int) → aliasNum aliases r ≠ st.base.nextVreg) :
    ∃ nx ny d,ctx.valueReg? x = some (.vreg nx .int) ∧ ctx.valueReg? y = some (.vreg ny .int) ∧
      out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        (signedCC cc) ty.width 32,
        .aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int)
          (if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)),
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        (signedCC cc) ty.width 32,
        .aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int)
          (if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)),
        .cset (.vreg d .int) (condOf cc)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
            VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
            ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY,producer,finish⟩ :=
    stock_cmp_narrow_rhs_observed hp ctx (signedCC cc) half cc typeX emitter
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  obtain ⟨ny,rfl⟩ := inv.valueReg y ry mapY
  have bits : ty.width = if half then 16 else 8 := by rw [sourceTy]; cases half <;> rfl
  have widths : ty.width = 8 ∨ ty.width = 16 := by rw [bits]; cases half <;> simp
  have demand := stock_apply_demand_mono conditionCall
  have neededX : Demanded next x := by
    have first := (mark_demand st x (extent x _ mapX)).1
    have second := stock_ctor_demand_mono (stock_put_in_reg ctx (st.mark x) y (.vreg ny .int) mapY safeY) x
    have last := demand x
    rw [finish] at last
    change ((st.mark x).mark y).demand[x]! ≤ next.demand[x]! at last
    unfold Demanded
    omega
  have neededY : Demanded next y := by
    have first := (mark_demand (st.mark x) y (by simpa only [State.mark,Array.size_modify] using extent y _ mapY)).1
    have last := demand y
    rw [finish] at last
    change ((st.mark x).mark y).demand[y]! ≤ next.demand[y]! at last
    unfold Demanded
    omega
  have heldX : ValuesHeld (fun z => z = x) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    intro z equal
    subst z
    exact held x neededX
  obtain ⟨ρ1,extensionRun,extended,kept⟩ := ScalarShift.stock_extend_resolved refines (signedCC cc)
    (widths.elim Or.inl (fun h => Or.inr (Or.inl h))) (to := 32) (d := st.base.nextVreg) (Or.inl rfl) (by omega)
    bounded mapX heldX getX
  have fresh : aliasNum aliases st.base.nextVreg = st.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have inputX : DivOpnd (signedCC cc) u (ρ1 (aliasNum aliases st.base.nextVreg)) := by
    rw [fresh]
    unfold DivOpnd
    simp only [show ty.width ≤ 32 by omega,ite_true]
    exact extended.2 (by change ty.width ≤ 32; omega)
  have inputY : (ρ1 (aliasNum aliases ny)).setWidth ty.width = v := by
    rw [kept _ (separatedY ny mapY)]
    exact held.read neededY (getAs_ok getY) mapY
  let e := if signedCC cc then (if half then ExtendOp.sxth else .sxtb) else (if half then ExtendOp.uxth else .uxtb)
  have decoded : MInst.ofV (.data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,
      .reg (.vreg st.base.nextVreg .int),.reg (.vreg ny .int),
      .data 84 (if signedCC cc then (if half then 5 else 4) else (if half then 1 else 0)) []]) =
      some (.aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int) e) := by
    dsimp only [e]
    cases signedCC cc <;> cases half <;> rfl
  have flagTruth := stock_cmp_narrow_extended_flags widths cc inputX inputY
  have eEq : (if signedCC cc then (if ty.width = 8 then ExtendOp.sxtb else .sxth)
      else (if ty.width = 8 then ExtendOp.uxtb else .uxth)) = e := by
    dsimp only [e]
    rw [bits]; cases signedCC cc <;> cases half <;> rfl
  rw [eEq] at flagTruth
  rw [producer] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by
    rw [finish]
    simp only [LState.fresh,LState.emit]
    omega
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_flag_condition_values hp ctx rfl enough
    decoded (condOf_ne_al cc) rfl conditionCall refines boundedMiddle
    (setsFlags_cmpExt .size32 st.base.nextVreg ny e (fun key => ρ1 (aliasNum aliases key))) flagTruth
  have first : Frag st.base middle.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) (signedCC cc) ty.width 32] := by
    rw [finish,← bits]
    exact Frag.fresh_emit st.base (by
      change vdefs (MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) (signedCC cc) ty.width 32) ⊆ _
      rw [vdefs_extend']; simp)
  have globalLower := Nat.le_trans first.mono lower
  refine ⟨nx,ny,d,mapX,mapY,output,globalLower,upper,first.append fragment,?_⟩
  intro world
  change Runs F isem (([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) (signedCC cc) ty.width 32] ++
    [MInst.aluRRRExtend .subS .size32 .xzr (.vreg st.base.nextVreg .int) (.vreg ny .int) e,.cset (.vreg d .int) (condOf cc)]).map _) _ _ _
  rw [List.map_append]
  refine (prun_runs extensionRun world (P := fun ρ2 _ => ρ2 = ρ1) (fun _ => rfl)).append (fun ρ2 world2 same => ?_)
  subst ρ2
  exact (execution world2).imp (fun ρ' _ _ ⟨value,frame⟩ => by
    refine ⟨value,?_⟩
    intro k outside
    have different : k ≠ d := by rcases outside with before | after <;> omega
    rw [frame k different]
    apply kept
    intro equal
    subst k
    rcases outside with before | after
    · omega
    · have := Nat.le_trans first.mono lower; omega)
end Backend.Stock.Proof.ScalarCmp

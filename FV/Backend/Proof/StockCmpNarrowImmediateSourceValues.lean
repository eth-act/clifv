import FV.Backend.Proof.StockExtendSemantics
import FV.Backend.Proof.StockCmpNarrowImmediateObserved
import FV.Backend.Proof.StockCmpNarrowMachineValues
import FV.Backend.Proof.StockDivConstant
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual5134 RHS and715 executions compute the original unsigned narrow
constant comparison, with the literal tied to original restricted DFG data.
The constant need not be materialized in a machine register. -/
theorem stock_cmp_narrow_immediate_condition_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) (half : Bool) (cc : Clif.IntCC)
    {ty : Clif.Ty} (sourceTy : ty = if half then .i16 else .i8)
    (unsigned : signedCC cc = false)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x y j : Nat} {info : IInfo} {literal : Int} {u v : BitVec ty.width}
    (getX : fr.getAs x ty = .ok u) (getY : fr.getAs y ty = .ok v)
    (defined : ctx.defInst? y = some j) (found : ctx.insts[j]? = some info)
    (data : info.data = .data 152 35 [.data 151 57 [],.int literal])
    {imm : Imm12} (encoded : Imm12.ofNat? (u64 literal) = some imm)
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    {st middle next : State} {tr emitTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enough : 119 ≤ fuel)
    (emitter : (evalExpr p (Stock.sem ctx) {} (n+160) rule_inst_5134.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),
        some (.value x),some (.op (.imm12 imm))]).run (st,tr) = .ok (some condition,middle,emitTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ nx d,ctx.valueReg? x = some (.vreg nx .int) ∧
      out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        false ty.width 32,
        .aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm,
        .cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs F isem ([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int)
        false ty.width 32,
        .aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm,
        .cset (.vreg d .int) (condOf cc)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
            VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc u v)⟩ (ρ' d) ∧
            ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  obtain ⟨_,constant⟩ := ScalarDiv.stock_div_constant_source_value inv dfg getY defined found data
  obtain ⟨literalValue,validImm⟩ := imm12_ofNat_value encoded (u64_lt literal)
  obtain ⟨safeX,rx,mapX,producer,finish⟩ := stock_cmp_narrow_immediate_rhs_observed hp ctx half cc typeX emitter
  obtain ⟨nx,rfl⟩ := inv.valueReg x rx mapX
  have bits : ty.width = if half then 16 else 8 := by rw [sourceTy]; cases half <;> rfl
  have widths : ty.width = 8 ∨ ty.width = 16 := by rw [bits]; cases half <;> simp
  rw [constant,u64_imm64OfIconst (by omega)] at literalValue
  have demand := stock_apply_demand_mono conditionCall
  have neededX : Demanded next x := by
    have first := (mark_demand st x (extent x _ mapX)).1
    have last := demand x
    rw [finish] at last
    change (st.mark x).demand[x]! ≤ next.demand[x]! at last
    unfold Demanded
    omega
  have heldX : ValuesHeld (fun z => z = x) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    intro z equal
    subst z
    exact held x neededX
  obtain ⟨ρ1,extensionRun,extended,kept⟩ := ScalarShift.stock_extend_resolved refines false
    (widths.elim Or.inl (fun h => Or.inr (Or.inl h))) (to := 32) (d := st.base.nextVreg) (Or.inl rfl) (by omega)
    bounded mapX heldX getX
  have fresh : aliasNum aliases st.base.nextVreg = st.base.nextVreg := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have inputX := extended.2 (show ty.width ≤ 32 by omega)
  change opnd .size32 (ρ1 st.base.nextVreg) = u.setWidth OperandSize.size32.bits at inputX
  have immediateValue : BitVec.ofNat 32 imm.value = v.setWidth 32 := by
    rw [literalValue]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,BitVec.toNat_setWidth]
  have flagTruth : condOn (condOf cc).bits (cmpFlags (opnd .size32 (ρ1 (aliasNum aliases st.base.nextVreg)))
      (BitVec.ofNat OperandSize.size32.bits imm.value)) = Clif.Sem.intcc cc u v := by
    rw [fresh,inputX]
    change condOn (condOf cc).bits (cmpFlags (u.setWidth 32) (BitVec.ofNat 32 imm.value)) = _
    rw [immediateValue,stock_cmp_conditions (Or.inl rfl)]
    exact stock_cmp_unsigned_extension (by omega) cc unsigned u v
  have decoded : MInst.ofV (.data 58 4 [.data 59 10 [],.data 93 0 [],.reg .xzr,
      .reg (.vreg st.base.nextVreg .int),.op (.imm12 imm)]) =
      some (.aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm) := rfl
  rw [producer] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by
    rw [finish]
    simp only [LState.fresh,LState.emit]
    omega
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_flag_condition_values hp ctx rfl enough
    decoded (condOf_ne_al cc) rfl conditionCall refines boundedMiddle
    (setsFlags_cmpImm .size32 st.base.nextVreg validImm (fun key => ρ1 (aliasNum aliases key))) flagTruth
  have first : Frag st.base middle.base [MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) false ty.width 32] := by
    rw [finish,← bits]
    exact Frag.fresh_emit st.base (by
      change vdefs (MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) false ty.width 32) ⊆ _
      rw [vdefs_extend']; simp)
  have globalLower := Nat.le_trans first.mono lower
  refine ⟨nx,d,mapX,output,globalLower,upper,first.append fragment,?_⟩
  intro world
  change Runs F isem (([MInst.extend (.vreg st.base.nextVreg .int) (.vreg nx .int) false ty.width 32] ++
    [MInst.aluRRImm12 .subS .size32 .xzr (.vreg st.base.nextVreg .int) imm,.cset (.vreg d .int) (condOf cc)]).map _) _ _ _
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

import FV.Backend.Proof.StockCmpNonzero8Emission
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockCmpTestFlags
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
theorem stock_cmp_nonzero8_rhs_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 8} (get : fr.getAs x .i8 = .ok u)
    (typed : ctx.valueType? x = some (.int 8))
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (emitter : (evalExpr p (Stock.sem ctx) {} (n+100) rule_inst_4988.rhs #[some (.value x)]).run
      (st,tr) = .ok (some condition,middle,emitterTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .ne] ∧
      ∀ world,Runs F isem ([MInst.aluRRImmLogic .andS .size32 .xzr (.vreg key .int) ⟨255,.size32⟩,.cset (.vreg d .int) .ne].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u != 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_nonzero8_rhs_observed hp ctx rfl emitter
  obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
  have needed : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapped)).1
    have grows := stock_apply_demand_mono conditionCall x
    rw [finish] at grows
    unfold Demanded
    omega
  have input := held.read needed (getAs_ok get) mapped
  have truth := stock_cmp_truthy8 u _ input
  rw [producer] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_flag_condition_values hp ctx rfl enoughCondition
    (ofV_tst .xzr (.vreg key .int) ⟨255,.size32⟩) (by decide) rfl conditionCall refines boundedMiddle
    (setsFlags_tst255 key (fun key => ρ (aliasNum aliases key))) truth
  refine ⟨key,d,mapped,output,?_,upper,?_,execution⟩
  · rw [finish] at lower; exact lower
  · rw [finish] at fragment; exact fragment
end Backend.Stock.Proof.ScalarCmp

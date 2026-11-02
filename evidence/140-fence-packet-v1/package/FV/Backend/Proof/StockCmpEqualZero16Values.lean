import FV.Backend.Proof.StockCmpNonzero16PrefixValues
import FV.Backend.Proof.StockCmpConditionValues
import FV.Backend.Proof.StockCmpZeroHelpers
import FV.Backend.Proof.StockDemandMono
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual16-bit extension-prefix and condition executions hold the original
source predicate and preserve all registers outside their real fresh interval. -/
theorem stock_cmp_equal_zero16_rhs_source_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} (dfg : DFGCons ctx fr) {x : Nat} {u : BitVec 16}
    (get : fr.getAs x .i16 = .ok u) {n inverseFuel fuel : Nat} (enoughCondition : 119 ≤ fuel) (enoughInverse : 39 ≤ inverseFuel)
    {st produced middle next : State} {tr emitterTrace inverseStart inverseTrace conditionStart trace : Array RuleId} {raw condition out : V}
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_4977.rhs
      #[some (.ty (.int 16)),some (.value x)]).run (st,tr) = .ok (some raw,produced,emitterTrace))
    (inversion : ApplyInternal p (Stock.sem ctx) {} inverseFuel 123 649 [raw]
      (produced,inverseStart) condition (middle,inverseTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ ms r d,out = .reg (.vreg d .int) ∧ st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base (ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .eq]) ∧
      ∀ world,Runs F isem ((ms ++ [cmpImm0 .size32 r,.cset (.vreg d .int) .eq]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u == 0)⟩ (ρ' d) ∧
          ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k) := by
  have prefixHeld : ValuesHeld (Demanded produced) ctx fr (fun key => ρ (aliasNum aliases key)) := by
    apply held.mono
    intro z needed
    have grows := stock_apply_demand_mono conditionCall z
    have inversionGrows := stock_apply_demand_mono inversion z
    unfold Demanded at needed ⊢
    omega
  obtain ⟨value,producer,prefixValues⟩ := stock_cmp_nonzero16_rhs_prefix_values hp inv dfg get rhs refines bounded extent prefixHeld
  obtain ⟨ms,r,ρ1,output,emitted,mono,defs,extExec,extended,kept⟩ := prefixValues
  rw [output] at producer
  rw [producer] at inversion
  obtain ⟨inverted,unchanged⟩ := stock_cmp_zero_invert_observed hp ctx enoughInverse true (.vreg r .int) (.data 93 0 []) inversion
  subst middle
  rw [inverted] at conditionCall
  have boundedMiddle : aliases.size ≤ produced.base.nextVreg := Nat.le_trans bounded mono
  obtain ⟨d,result,lower,upper,fragment,execution⟩ := stock_cmp_zero_condition_values hp ctx rfl enoughCondition false .size32 rfl
    conditionCall refines boundedMiddle (ρ := ρ1)
  simp only [Bool.false_eq_true,ite_false] at execution fragment
  have wide := extended.2 (by change 16 ≤ 32; decide)
  change opnd .size32 (ρ1 (aliasNum aliases r)) = u.setWidth OperandSize.size32.bits at wide
  rw [wide] at execution
  have truth : (u.setWidth OperandSize.size32.bits == 0) = (u == 0) := by
    have nonzero := truthy_setWidth32 (by decide) u
    change (u.setWidth 32 == 0) = (u == 0)
    change (!(u.setWidth 32 == 0)) = (!(u == 0)) at nonzero
    exact Bool.not_inj nonzero
  rw [truth] at execution
  have first : Frag st.base produced.base ms := ⟨emitted,mono,defs⟩
  refine ⟨ms,r,d,result,Nat.le_trans mono lower,upper,first.append fragment,?_⟩
  intro world
  rw [List.map_append]
  refine (prun_runs extExec world (P := fun ρ2 _ => ρ2 = ρ1) (fun _ => rfl)).append (fun ρ2 world2 same => ?_)
  subst ρ2
  exact (execution world2).imp (fun ρ' _ _ ⟨value,frame⟩ => by
    refine ⟨value,?_⟩
    intro k outside
    have different : k ≠ d := by rcases outside with before | after <;> omega
    rw [frame k different]
    apply kept
    rcases outside with before | after
    · exact Or.inl before
    · exact Or.inr (Nat.le_trans fragment.mono after))
end Backend.Stock.Proof.ScalarCmp

module

public import FV.Backend.Proof.StockCmpNonzeroNarrowCalls

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Real32-bit nonzero RHS execution derives its guarded mapping, exact
condition and complete marked state from the actual zero-extension call. -/
theorem stock_cmp_nonzero32_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {x n : Nat} (typed : ctx.valueType? x = some (.int 32))
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_4977.rhs
      #[some (.ty (.int 32)),some (.value x)]).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
      out = .data 123 1 [.reg rx,.data 93 0 []] ∧ next = st.mark x := by
  obtain ⟨fuel,value,enough,extension,output⟩ := stock_cmp_nonzero_narrow_rhs_calls hp ctx x (.int 32) n run
  obtain ⟨t,type,safe,rx,mapped,form⟩ := ScalarShift.stock_zext32_out hp rfl enough extension
  simp only [typed,Option.some.injEq] at type
  subst t
  rcases form with ⟨passes,rfl,finish⟩ | ⟨notPass,_,_,_⟩
  · exact ⟨safe,rx,mapped,output,finish⟩
  · exact False.elim (notPass (by simp))
/-- The real32-bit RHS and715 call hold the original32-bit source predicate
through final aliases, with fresh-write and other-register preservation. -/
theorem stock_cmp_nonzero32_rhs_values {p : Program} (hp : Data p)
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {fr : Clif.Frame} {x : Nat} {u : BitVec 32} (get : fr.getAs x .i32 = .ok u)
    (typed : ctx.valueType? x = some (.int 32))
    {st middle next : State} {tr emitterTrace conditionStart trace : Array RuleId}
    {n fuel : Nat} {condition out : V} (enoughCondition : 119 ≤ fuel)
    (rhs : (evalExpr p (Stock.sem ctx) {} (n+220) rule_inst_4977.rhs
      #[some (.ty (.int 32)),some (.value x)]).run (st,tr) = .ok (some condition,middle,emitterTrace))
    (conditionCall : ApplyInternal p (Stock.sem ctx) {} fuel 27 715 [condition]
      (middle,conditionStart) out (next,trace))
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (extent : ∀ z r,ctx.valueReg? z = some r → z < st.demand.size)
    (held : ValuesHeld (Demanded next) ctx fr (fun key => ρ (aliasNum aliases key))) :
    ∃ key d,ctx.valueReg? x = some (.vreg key .int) ∧ out = .reg (.vreg d .int) ∧
      st.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag st.base next.base [cmpImm0 .size32 key,.cset (.vreg d .int) .ne] ∧
      ∀ world,Runs F isem ([cmpImm0 .size32 key,.cset (.vreg d .int) .ne].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (u != 0)⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = ρ k) := by
  obtain ⟨safe,rx,mapped,producer,finish⟩ := stock_cmp_nonzero32_rhs_observed hp ctx typed rhs
  obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
  have needed : Demanded next x := by
    have marked := (mark_demand st x (extent x _ mapped)).1
    have grows := stock_apply_demand_mono conditionCall x
    rw [finish] at grows
    unfold Demanded
    omega
  have input := held.read needed (getAs_ok get) mapped
  have word : opnd .size32 (ρ (aliasNum aliases key)) = u := by
    change (ρ (aliasNum aliases key)).setWidth 32 = u at input
    change ((ρ (aliasNum aliases key)).setWidth 64).setWidth 32 = u
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    exact input
  rw [producer] at conditionCall
  have boundedMiddle : aliases.size ≤ middle.base.nextVreg := by rw [finish]; exact bounded
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero_condition_values hp ctx rfl enoughCondition true .size32 rfl
    conditionCall refines boundedMiddle
  simp only [ite_true] at execution fragment
  rw [word] at execution
  refine ⟨key,d,mapped,output,?_,upper,?_,execution⟩
  · rw [finish] at lower; exact lower
  · rw [finish] at fragment; exact fragment
end Backend.Stock.Proof.ScalarCmp

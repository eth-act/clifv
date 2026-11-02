import FV.Backend.Proof.StockDivSignedObservations
import FV.Backend.Proof.StockDivIntmin
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Actual minimum-check preparation executes through final aliases, reflects
original signed source minimum values, and preserves every outside register. -/
theorem stock_div_minimum_source_values {p : Program} (hp : Data p) (ctx : Ctx)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {n fuel key : Nat} (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (enough : 59 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 27 562 [.ty (.int n),.reg (.vreg key .int)]
      (st,tr) out (next,trace))
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {u : BitVec n}
    (bounded : aliases.size ≤ st.base.nextVreg)
    (operand : DivOpnd true u (ρ (aliasNum aliases key))) :
    ∃ ms check ρ',out = .reg (.vreg check .int) ∧ Frag st.base next.base ms ∧
      (check = key ∨ st.base.nextVreg ≤ check ∧ check < next.base.nextVreg) ∧
      PRun F isem (ms.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ ρ' ∧
      (opnd (szOf n) (ρ' (aliasNum aliases check)) = BitVec.intMin (szOf n).bits ↔ u = BitVec.intMin n) ∧
      ∀ k,k < st.base.nextVreg ∨ next.base.nextVreg ≤ k → ρ' k = ρ k := by
  obtain ⟨output,finish⟩ := stock_div_intmin_observed hp ctx rfl enough width run
  by_cases small : n ≤ 16
  · simp only [small,ite_true] at output finish
    let d := st.base.nextVreg
    let value := resX .size32 (opnd .size32 (ρ (aliasNum aliases key)) <<< (32-n))
    have fresh : aliasNum aliases d = d := by
      apply chaseF_none
      rw [Array.getElem?_eq_none bounded]
      rfl
    let inst : MInst := .aluRRImmShift .lsl .size32 (.vreg d .int) (.vreg key .int) (32-n)
    have code : inst.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
        .aluRRImmShift .lsl .size32 (.vreg d .int) (.vreg (aliasNum aliases key) .int) (32-n) := by
      simp only [inst,MInst.mapRegs,resolve_vreg]
      change MInst.aluRRImmShift .lsl .size32 (.vreg (aliasNum aliases d) .int)
        (.vreg (aliasNum aliases key) .int) (32-n) = _
      rw [fresh]
    have fragment : Frag st.base next.base [inst] := by
      rw [finish]
      exact Frag.fresh_emit st.base (by
        change vdefs (.aluRRImmShift .lsl .size32 (.vreg st.base.nextVreg .int) (.vreg key .int) (32-n)) ⊆ _
        rw [vdefs_lsl']; simp)
    have execution : PRun F isem [inst.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ (upd ρ d value) := by
      rw [code]
      exact prun_rr refines rfl (fun world => by
        show ispec _ [ρ (aliasNum aliases key)] world = _
        simp [ispec,shiftVal,defOut,OperandSize.bits,show 32-n < 32 from by omega,value]) (prun_nil _)
    refine ⟨[inst],d,upd ρ d value,output,fragment,Or.inr ?_,execution,?_,?_⟩
    · rw [finish]; simp [d,LState.fresh,LState.emit]
    · rw [fresh,upd_same]
      unfold DivOpnd at operand
      rcases width with rfl | rfl | rfl | rfl <;> (try omega)
      · simp only [show (8:Nat) ≤ 32 by decide,ite_true] at operand
        change opnd .size32 (resX .size32 (opnd .size32 (ρ (aliasNum aliases key)) <<< 24)) = BitVec.intMin 32 ↔ _
        rw [cmp_opnd_resX,show opnd .size32 (ρ (aliasNum aliases key)) = (lo64 (ρ (aliasNum aliases key))).setWidth 32 from rfl,operand]
        exact stock_div_shift_intMin (Or.inl rfl) u
      · simp only [show (16:Nat) ≤ 32 by decide,ite_true] at operand
        change opnd .size32 (resX .size32 (opnd .size32 (ρ (aliasNum aliases key)) <<< 16)) = BitVec.intMin 32 ↔ _
        rw [cmp_opnd_resX,show opnd .size32 (ρ (aliasNum aliases key)) = (lo64 (ρ (aliasNum aliases key))).setWidth 32 from rfl,operand]
        exact stock_div_shift_intMin (Or.inr rfl) u
    · intro k outside
      have count : next.base.nextVreg = d+1 := by rw [finish]; rfl
      simp [upd,show k ≠ d from by omega]
  · simp only [small,ite_false] at output finish
    refine ⟨[],key,ρ,output,?_,Or.inl rfl,prun_nil _,?_,fun _ _ => rfl⟩
    · rw [finish]; exact Frag.nil _
    · exact divOpnd_intMin (by omega) operand
end Backend.Stock.Proof.ScalarDiv

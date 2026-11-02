import FV.Backend.Proof.IselFamAluBBase
import FV.Backend.Proof.StockAliasSemantics
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem fresh_reg {aliases : Array (Option Nat)} {d : Nat} (bounded : aliases.size ≤ d) :
    Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int) = .vreg d .int := by
  rw [resolve_vreg]
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]; rfl
  change Reg.vreg (aliasNum aliases d) .int = _
  rw [fresh]
/-- Actual quotient emission executes through final aliases and preserves every
register except its fresh destination. Zero/overflow guards remain separate. -/
theorem stock_div_quotient_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (signed : Bool) (sz : OperandSize)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a b d : Nat} (bounded : aliases.size ≤ d) :
    ∃ ρ',PRun F isem
      [(MInst.aluRRR (if signed then .sDiv else .uDiv) sz (.vreg d .int) (.vreg a .int) (.vreg b .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      ρ' d = resX sz (if signed then (opnd sz (ρ (aliasNum aliases a))).sdiv (opnd sz (ρ (aliasNum aliases b)))
        else opnd sz (ρ (aliasNum aliases a)) / opnd sz (ρ (aliasNum aliases b))) ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  let value := if signed then (opnd sz (ρ (aliasNum aliases a))).sdiv (opnd sz (ρ (aliasNum aliases b)))
    else opnd sz (ρ (aliasNum aliases a)) / opnd sz (ρ (aliasNum aliases b))
  have code : (MInst.aluRRR (if signed then .sDiv else .uDiv) sz (.vreg d .int) (.vreg a .int) (.vreg b .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRR (if signed then .sDiv else .uDiv) sz (.vreg d .int)
        (.vreg (aliasNum aliases a) .int) (.vreg (aliasNum aliases b) .int) := by
    change MInst.aluRRR _ sz (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg a .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg b .int)) = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg]; rfl
  refine ⟨upd ρ d (resX sz value),?_,upd_same _ _ _,?_⟩
  · rw [code]
    have spec : ∀ world,ispec (.aluRRR (if signed then .sDiv else .uDiv) sz (.vreg d .int)
      (.vreg (aliasNum aliases a) .int) (.vreg (aliasNum aliases b) .int))
      [ρ (aliasNum aliases a),ρ (aliasNum aliases b)] world = some ([resX sz value],world,.next) := by
      intro world; cases signed <;> rfl
    exact prun_rrr refines rfl spec (prun_nil _)
  · intro n different; simp only [upd,different,ite_false]
/-- Actual multiply-subtract emission resolves every operand and leaves all
other registers unchanged, including the prior source operands. -/
theorem stock_div_msub_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (sz : OperandSize)
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {a b c d : Nat} (bounded : aliases.size ≤ d) :
    ∃ ρ',PRun F isem
      [(MInst.aluRRRR .mSub sz (.vreg d .int) (.vreg a .int) (.vreg b .int) (.vreg c .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ ρ' ∧
      ρ' d = resX sz (opnd sz (ρ (aliasNum aliases c)) -
        opnd sz (ρ (aliasNum aliases a))*opnd sz (ρ (aliasNum aliases b))) ∧
      ∀ n,n ≠ d → ρ' n = ρ n := by
  let value := opnd sz (ρ (aliasNum aliases c)) - opnd sz (ρ (aliasNum aliases a))*opnd sz (ρ (aliasNum aliases b))
  have code : (MInst.aluRRRR .mSub sz (.vreg d .int) (.vreg a .int) (.vreg b .int) (.vreg c .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .aluRRRR .mSub sz (.vreg d .int) (.vreg (aliasNum aliases a) .int)
        (.vreg (aliasNum aliases b) .int) (.vreg (aliasNum aliases c) .int) := by
    change MInst.aluRRRR _ sz (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg a .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg b .int))
      (Backend.lowerFunction.resolve aliases (aliases.size+1) (.vreg c .int)) = _
    rw [fresh_reg bounded,resolve_vreg,resolve_vreg,resolve_vreg]; rfl
  refine ⟨upd ρ d (resX sz value),?_,upd_same _ _ _,?_⟩
  · rw [code]
    exact prun_cons refines (ops := #[⟨d,.int,.def,.late,.reg⟩,
      ⟨aliasNum aliases a,.int,.use,.early,.reg⟩,⟨aliasNum aliases b,.int,.use,.early,.reg⟩,
      ⟨aliasNum aliases c,.int,.use,.early,.reg⟩]) rfl (fun _ => rfl) rfl (prun_nil _)
  · intro n different; simp only [upd,different,ite_false]
end Backend.Stock.Proof.ScalarDiv

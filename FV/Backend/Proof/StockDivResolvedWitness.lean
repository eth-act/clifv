module

public import FV.Backend.Proof.StockDivResolved

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def witnessAliases : Array (Option Nat) := #[some 1,none,none]
private def witnessRegs (sz : OperandSize) (n : Nat) : CV :=
  if n = 1 then resX sz (BitVec.ofNat sz.bits 7) else
    if n = 2 then resX sz (BitVec.ofNat sz.bits 3) else 0
/-- Signed/unsigned32/64 division followed by multiply-subtract is inhabited
through a nontrivial source alias, with concrete quotient2/remainder1. -/
theorem stock_div_resolved_witness (signed : Bool) (sz : OperandSize) :
    ∃ ρ1 ρ2,PRun (fun _ => True) ispec
      [(MInst.aluRRR (if signed then .sDiv else .uDiv) sz (.vreg 3 .int) (.vreg 0 .int) (.vreg 2 .int)).mapRegs
        (Backend.lowerFunction.resolve witnessAliases (witnessAliases.size+1))] (witnessRegs sz) ρ1 ∧
      PRun (fun _ => True) ispec
      [(MInst.aluRRRR .mSub sz (.vreg 4 .int) (.vreg 3 .int) (.vreg 2 .int) (.vreg 0 .int)).mapRegs
        (Backend.lowerFunction.resolve witnessAliases (witnessAliases.size+1))] ρ1 ρ2 ∧
      ρ1 3 = resX sz (BitVec.ofNat sz.bits 2) ∧ ρ2 4 = resX sz (BitVec.ofNat sz.bits 1) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ1,exec1,value1,kept1⟩ := stock_div_quotient_resolved self signed sz
    (aliases := witnessAliases) (ρ := witnessRegs sz) (a := 0) (b := 2) (d := 3) (by decide)
  have q : ρ1 3 = resX sz (BitVec.ofNat sz.bits 2) := by
    rw [value1]
    cases signed <;> cases sz <;> decide +kernel
  obtain ⟨ρ2,exec2,value2,kept2⟩ := stock_div_msub_resolved self sz
    (aliases := witnessAliases) (ρ := ρ1) (a := 3) (b := 2) (c := 0) (d := 4) (by decide)
  have aliases0 : aliasNum witnessAliases 0 = 1 := by decide +kernel
  have aliases2 : aliasNum witnessAliases 2 = 2 := by decide +kernel
  have aliases3 : aliasNum witnessAliases 3 = 3 := by decide +kernel
  have rem : ρ2 4 = resX sz (BitVec.ofNat sz.bits 1) := by
    rw [value2,aliases0,aliases2,aliases3,q,kept1 1 (by decide),kept1 2 (by decide)]
    cases sz <;> decide +kernel
  exact ⟨ρ1,ρ2,exec1,exec2,q,rem⟩
end Backend.Stock.Proof.ScalarDiv

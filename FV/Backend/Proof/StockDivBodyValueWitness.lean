import FV.Backend.Proof.StockDivBodyValues
namespace Backend.Stock.Proof.ScalarDiv.BodyValueWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def aliases : Array (Option Nat) := #[some 1,none,none]
private def numerator (ty : Clif.Ty) := BitVec.ofInt ty.width (-7)
private def denominator (ty : Clif.Ty) := BitVec.ofNat ty.width 3
private def quotient (signed : Bool) (ty : Clif.Ty) : BitVec ty.width :=
  if signed then (numerator ty).sdiv (denominator ty) else numerator ty / denominator ty
private def remainder (signed : Bool) (ty : Clif.Ty) : BitVec ty.width :=
  if signed then (numerator ty).srem (denominator ty) else numerator ty % denominator ty
private def regs (signed : Bool) (ty : Clif.Ty) (n : Nat) : CV :=
  if n = 1 then resX (szOf ty.width) (if signed then (numerator ty).signExtend (szOf ty.width).bits
      else (numerator ty).zeroExtend (szOf ty.width).bits)
  else if n = 2 then resX (szOf ty.width) (if signed then (denominator ty).signExtend (szOf ty.width).bits
      else (denominator ty).zeroExtend (szOf ty.width).bits) else 0
/-- Signed/unsigned source quotient and remainder semantics are inhabited at
8/16/32/64 with a negative original numerator, aliased source registers and
fresh outputs; all unaffected machine registers are preserved. -/
theorem stock_div_source_body_witness (signed : Bool) (ty : Clif.Ty)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ ρq ρr,PRun (fun _ => True) ispec
      [(MInst.aluRRR (if signed then .sDiv else .uDiv) (szOf ty.width) (.vreg 3 .int) (.vreg 0 .int) (.vreg 2 .int)).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] (regs signed ty) ρq ∧
      VHolds ⟨ty,quotient signed ty⟩ (ρq 3) ∧ (∀ k,k ≠ 3 → ρq k = regs signed ty k) ∧
      PRun (fun _ => True) ispec
        ([MInst.aluRRR (if signed then .sDiv else .uDiv) (szOf ty.width) (.vreg 3 .int) (.vreg 0 .int) (.vreg 2 .int),
          MInst.aluRRRR .mSub (szOf ty.width) (.vreg 4 .int) (.vreg 3 .int) (.vreg 2 .int) (.vreg 0 .int)].map
          (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) (regs signed ty) ρr ∧
      VHolds ⟨ty,remainder signed ty⟩ (ρr 4) ∧ (∀ k,k < 3 ∨ 5 ≤ k → ρr k = regs signed ty k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64 := by
    rcases supported with rfl | rfl | rfl | rfl <;> simp [Clif.Ty.width]
  have sourceQ : Clif.Sem.div (if signed then .sdiv else .udiv) (numerator ty) (denominator ty) =
      .ok (quotient signed ty) := by
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceR : Clif.Sem.div (if signed then .srem else .urem) (numerator ty) (denominator ty) =
      .ok (remainder signed ty) := by
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have inputX : DivOpnd signed (numerator ty) (regs signed ty (aliasNum aliases 0)) := by
    unfold DivOpnd
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
  have inputY : DivOpnd signed (denominator ty) (regs signed ty (aliasNum aliases 2)) := by
    unfold DivOpnd
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
  obtain ⟨ρq,execQ,valueQ,keptQ⟩ := stock_div_quotient_source_values self signed width sourceQ
    (aliases := aliases) (ρ := regs signed ty) (a := 0) (b := 2) (d := 3) (by decide) inputX inputY
  obtain ⟨ρr,execR,valueR,keptR⟩ := stock_div_remainder_source_values self signed width sourceR
    (aliases := aliases) (ρ := regs signed ty) (a := 0) (b := 2) (d := 3) (by decide) (by decide) (by decide) inputX inputY
  exact ⟨ρq,ρr,execQ,valueQ,keptQ,execR,valueR,keptR⟩
end Backend.Stock.Proof.ScalarDiv.BodyValueWitness

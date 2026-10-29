module

public import FV.Backend.Proof.StockCmpMachineValues

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
inductive Boundary where
  | equalZero | zeroOne | oneZero | minusOneOne | minimumMinusOne | maximumMinimum
  deriving DecidableEq
private def leftValue (n : Nat) : Boundary → BitVec n
  | .equalZero | .zeroOne => 0
  | .oneZero => 1
  | .minusOneOne => -1
  | .minimumMinusOne => BitVec.intMin n
  | .maximumMinimum => BitVec.intMax n
private def rightValue (n : Nat) : Boundary → BitVec n
  | .equalZero | .oneZero => 0
  | .zeroOne | .minusOneOne => 1
  | .minimumMinusOne => -1
  | .maximumMinimum => BitVec.intMin n
private def fixtureAliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def extended (cc : Clif.IntCC) (n : Nat) (v : BitVec n) : CV :=
  resX (szOf n) (if signedCC cc then v.signExtend (szOf n).bits else v.zeroExtend (szOf n).bits)
private def fixtureRegs (cc : Clif.IntCC) (n : Nat) (boundary : Boundary) (key : Nat) : CV :=
  if key = 1 then extended cc n (leftValue n boundary)
  else if key = 3 then extended cc n (rightValue n boundary) else 0
/-- Real mapped compare/cset instructions inhabit all ten predicates at all four
source widths and six signed/unsigned boundaries, including both overflow regions. -/
theorem stock_cmp_alias_machine_witness (cc : Clif.IntCC) (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (boundary : Boundary) (world : Arm.ArmState) :
    ∃ ρ,Runs (fun _ => True) ispec ([MInst.aluRRR .subS (szOf n) .xzr (.vreg 0 .int) (.vreg 2 .int),
      .cset (.vreg 4 .int) (condOf cc)].map (·.mapRegs
        (Backend.lowerFunction.resolve fixtureAliases (fixtureAliases.size+1)))) ρ world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc (leftValue n boundary) (rightValue n boundary))⟩ (ρ' 4) ∧
          ∀ k,k ≠ 4 → ρ' k = ρ k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have inputA : DivOpnd (signedCC cc) (leftValue n boundary)
      (fixtureRegs cc n boundary (aliasNum fixtureAliases 0)) := by
    unfold DivOpnd
    cases cc <;> cases boundary <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  have inputB : DivOpnd (signedCC cc) (rightValue n boundary)
      (fixtureRegs cc n boundary (aliasNum fixtureAliases 2)) := by
    unfold DivOpnd
    cases cc <;> cases boundary <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel
  exact ⟨fixtureRegs cc n boundary,stock_cmp_rr_resolved self width cc (by decide) inputA inputB world⟩
/-- The exact guarded predecessor premises are inhabited at both machine
widths; ordinary source operands retain the original unsigned/signed outcomes. -/
theorem stock_cmp_predecessor_witness (n : Nat) (width : n = 32 ∨ n = 64) :
    ∃ a b : BitVec n,b ≠ 0 ∧ b ≠ BitVec.intMin n ∧
      condOn Cond.hi.bits (cmpFlags a (b-1)) = Clif.Sem.intcc .uge a b ∧
      condOn Cond.gt.bits (cmpFlags a (b-1)) = Clif.Sem.intcc .sge a b := by
  let a : BitVec n := 7
  let b : BitVec n := 3
  have nonzero : b ≠ 0 := by rcases width with rfl | rfl <;> decide +kernel
  have notMinimum : b ≠ BitVec.intMin n := by rcases width with rfl | rfl <;> decide +kernel
  exact ⟨a,b,nonzero,notMinimum,stock_cmp_unsigned_predecessor width a b nonzero,
    stock_cmp_signed_predecessor width a b notMinimum⟩
/-- Narrow signed/unsigned comparison-extension contracts have real original
operands at8/16/32 and every condition in the matching condition family. -/
theorem stock_cmp_extension_witness (cc : Clif.IntCC) (n : Nat)
    (width : n = 8 ∨ n = 16 ∨ n = 32) :
    ∃ a b : BitVec n,(signedCC cc = true →
      Clif.Sem.intcc cc (a.signExtend 32) (b.signExtend 32) = Clif.Sem.intcc cc a b) ∧
      (signedCC cc = false →
      Clif.Sem.intcc cc (a.zeroExtend 32) (b.zeroExtend 32) = Clif.Sem.intcc cc a b) :=
  ⟨BitVec.intMin n,-1,(fun signed => stock_cmp_signed_extension (n := n) (m := 32) (by omega) cc signed _ _),
    (fun unsigned => stock_cmp_unsigned_extension (n := n) (m := 32) (by omega) cc unsigned _ _)⟩
end Backend.Stock.Proof.ScalarCmp

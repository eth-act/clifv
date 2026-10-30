import FV.Backend.Proof.IselCmpDivRoot
import FV.Backend.Proof.StockCmpConditionValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def fixtureState : State := {sinkState with base := {sinkState.base with nextVreg := 4}}
private def fixtureAliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def sizeIndex : OperandSize → Nat | .size32 => 0 | .size64 => 1
private def wordRegs (sz : OperandSize) (zero : Bool) (_ : Nat) : CV :=
  BitVec.ofNat 128 (2^100+(if zero then 0 else 7))
/-- Every real Zero/NotZero helper at32/64 has inhabited original input/output
states and both boolean outcomes, with dirty upper bits and a nonidentity alias. -/
theorem stock_cmp_zero_condition_witness (nonzero zero : Bool) (sz : OperandSize) :
    ∃ out next trace d,ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 (if nonzero then 1 else 0) [.reg (.vreg 0 .int),.data 93 (sizeIndex sz) []]]
      (fixtureState,#[]) out (next,trace) ∧
      out = .reg (.vreg d .int) ∧ fixtureState.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag fixtureState.base next.base [cmpImm0 sz 0,.cset (.vreg d .int) (if nonzero then .ne else .eq)] ∧
      ∀ world,Runs (fun _ => True) ispec ([cmpImm0 sz 0,.cset (.vreg d .int) (if nonzero then .ne else .eq)].map
        (·.mapRegs (Backend.lowerFunction.resolve fixtureAliases (fixtureAliases.size+1)))) (wordRegs sz zero) world
        (fun ρ' _ => VHolds ⟨.i8,Clif.Sem.bool8 (if nonzero then !zero else zero)⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = wordRegs sz zero k) := by
  obtain ⟨trace,run⟩ := stock_cmp_condition_zero data_program sinkCtx (cfg := {}) rfl nonzero sz fixtureState #[] 880 (.vreg 0 .int)
  have actual := run
  change ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 (if nonzero then 1 else 0) [.reg (.vreg 0 .int),.data 93 (sizeIndex sz) []]]
      (fixtureState,#[]) _ (_,trace) at actual
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have size : OperandSize.ofIdx? (sizeIndex sz) = some sz := by cases sz <;> rfl
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_zero_condition_values data_program sinkCtx rfl
    (by decide) nonzero sz size actual self (aliases := fixtureAliases) (by decide) (ρ := wordRegs sz zero)
  have truth : (if nonzero then opnd sz (wordRegs sz zero (aliasNum fixtureAliases 0)) != 0
      else opnd sz (wordRegs sz zero (aliasNum fixtureAliases 0)) == 0) = (if nonzero then !zero else zero) := by
    cases nonzero <;> cases zero <;> cases sz <;> decide +kernel
  rw [truth] at execution
  exact ⟨_,_,trace,d,actual,output,lower,upper,fragment,execution⟩
private def producer (sz : OperandSize) : V :=
  .data 58 2 [.data 59 10 [],.data 93 (sizeIndex sz) [],.reg .xzr,.reg (.vreg 0 .int),.reg (.vreg 2 .int)]
private def compareRegs (sz : OperandSize) (key : Nat) : CV :=
  if key = 1 then resX sz (BitVec.intMin sz.bits)
  else if key = 3 then resX sz (BitVec.allOnes sz.bits) else 0
/-- Real explicit-flag helper execution inhabits all ten conditions at both
machine widths through nonidentity aliases and fresh result allocation. -/
theorem stock_cmp_flag_condition_witness (sz : OperandSize) (cc : Clif.IntCC) :
    ∃ out next trace d,ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 2 [.data 47 1 [producer sz],.data 96 (condOf cc).idx []]]
      (fixtureState,#[]) out (next,trace) ∧
      out = .reg (.vreg d .int) ∧ fixtureState.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag fixtureState.base next.base [.aluRRR .subS sz .xzr (.vreg 0 .int) (.vreg 2 .int),.cset (.vreg d .int) (condOf cc)] ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRR .subS sz .xzr (.vreg 0 .int) (.vreg 2 .int),.cset (.vreg d .int) (condOf cc)].map
        (·.mapRegs (Backend.lowerFunction.resolve fixtureAliases (fixtureAliases.size+1)))) (compareRegs sz) world
        (fun ρ' _ => VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc cc (BitVec.intMin sz.bits) (BitVec.allOnes sz.bits))⟩ (ρ' d) ∧
          ∀ k,k ≠ d → ρ' k = compareRegs sz k) := by
  have decoded : MInst.ofV (producer sz) = some (.aluRRR .subS sz .xzr (.vreg 0 .int) (.vreg 2 .int)) := by
    cases sz <;> rfl
  obtain ⟨trace,run⟩ := stock_cmp_condition_flags data_program sinkCtx (cfg := {}) rfl fixtureState #[] 880 decoded (condOf cc)
  have actual : ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 2 [.data 47 1 [producer sz],.data 96 (condOf cc).idx []]] (fixtureState,#[]) _ (_,trace) := run
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have flags := setsFlags_cmpRR sz 0 2 (fun key => compareRegs sz (aliasNum fixtureAliases key))
  have truth : condOn (condOf cc).bits (cmpFlags
      (opnd sz (compareRegs sz (aliasNum fixtureAliases 0)))
      (opnd sz (compareRegs sz (aliasNum fixtureAliases 2)))) =
      Clif.Sem.intcc cc (BitVec.intMin sz.bits) (BitVec.allOnes sz.bits) := by
    have original := stock_cmp_conditions (n := sz.bits) (by cases sz <;> simp [OperandSize.bits]) cc
      (BitVec.intMin sz.bits) (BitVec.allOnes sz.bits)
    have leftAlias : aliasNum fixtureAliases 0 = 1 := by decide +kernel
    have rightAlias : aliasNum fixtureAliases 2 = 3 := by decide +kernel
    rw [leftAlias,rightAlias]
    simpa only [compareRegs,ite_true,ite_false,Nat.reduceEqDiff,cmp_opnd_resX] using original
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_flag_condition_values data_program sinkCtx rfl
    (by decide) decoded (condOf_ne_al cc) rfl actual self (by decide) flags truth
  exact ⟨_,_,trace,d,actual,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp

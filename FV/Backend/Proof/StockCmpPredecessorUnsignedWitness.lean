import FV.Backend.Proof.StockCmpPredecessorUnsignedValues
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def fixtureState : State := {sinkState with base := {sinkState.base with nextVreg := 4}}
private def fixtureAliases : Array (Option Nat) := #[some 1,none,some 3,none]
private def fixtureRegs (_ : Nat) : CV := BitVec.ofNat 128 (2^100+7)
private def literal (shift : Bool) : Imm12 := ⟨2,shift⟩
private def producer (sz : OperandSize) (shift : Bool) : V :=
  .data 58 4 [.data 59 10 [],.data 93 (if sz = .size32 then 0 else 1) [],
    .reg .xzr,.reg (.vreg 0 .int),.op (.imm12 (literal shift))]
/-- Both immediate encoding forms, both machine widths and all integer
conditions have real helper executions with dirty upper bits and final aliases. -/
theorem stock_cmp_predecessor_unsigned_condition_witness (sz : OperandSize) (shift : Bool) :
    ∃ out next trace d,ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 2 [.data 47 1 [producer sz shift],.data 96 (condOf .ugt).idx []]]
      (fixtureState,#[]) out (next,trace) ∧
      out = .reg (.vreg d .int) ∧ fixtureState.base.nextVreg ≤ d ∧ d < next.base.nextVreg ∧
      Frag fixtureState.base next.base [.aluRRImm12 .subS sz .xzr (.vreg 0 .int) (literal shift),
        .cset (.vreg d .int) (condOf .ugt)] ∧
      ∀ world,Runs (fun _ => True) ispec ([MInst.aluRRImm12 .subS sz .xzr (.vreg 0 .int) (literal shift),
        .cset (.vreg d .int) (condOf .ugt)].map
        (·.mapRegs (Backend.lowerFunction.resolve fixtureAliases (fixtureAliases.size+1)))) fixtureRegs world
        (fun ρ' _ => VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .uge (BitVec.ofNat sz.bits 7)
          (BitVec.ofNat sz.bits ((literal shift).value+1)))⟩ (ρ' d) ∧ ∀ k,k ≠ d → ρ' k = fixtureRegs k) := by
  have decoded : MInst.ofV (producer sz shift) =
      some (.aluRRImm12 .subS sz .xzr (.vreg 0 .int) (literal shift)) := by cases sz <;> rfl
  obtain ⟨trace,run⟩ := stock_cmp_condition_flags data_program sinkCtx (cfg := {}) rfl fixtureState #[] 880 decoded (condOf .ugt)
  have actual : ApplyInternal program (Stock.sem sinkCtx) {} 999 27 715
      [.data 123 2 [.data 47 1 [producer sz shift],.data 96 (condOf .ugt).idx []]]
      (fixtureState,#[]) _ (_,trace) := run
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have input : opnd sz (fixtureRegs (aliasNum fixtureAliases 0)) = BitVec.ofNat sz.bits 7 := by
    cases sz <;> decide +kernel
  have valid : (literal shift).bits < 4096 := by simp [literal]
  obtain ⟨d,output,lower,upper,fragment,execution⟩ := stock_cmp_predecessor_unsigned_condition_values data_program sinkCtx sz (v := BitVec.ofNat sz.bits ((literal shift).value+1))
    valid (by decide) actual self (by decide)
    (by cases sz <;> cases shift <;> decide +kernel)
    (by cases sz <;> cases shift <;> decide +kernel) input
  exact ⟨_,_,trace,d,actual,output,lower,upper,fragment,execution⟩
end Backend.Stock.Proof.ScalarCmp

import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockTwoBlockTrap
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.TwoBlockTrapWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

private def function : Clif.Function := {
  name := "stock_two_block_source_trap"
  sig := {params := [{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64)],body := [⟨[1],.iconst .i64 0⟩,⟨[],.nop⟩],term := .jump ⟨10,[1]⟩},
    {id := 10,params := [(2,.i64)],body := [⟨[3],.div .udiv .i64 0 2⟩],term := .ret [3]}] }

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
-- witness: native_decide (fixed original input dominance only)
private theorem dominated : Dominated function := dominated_of (by native_decide)
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower Stock.runTerm
private theorem compiled : (Stock.lower function).isOk = true := by decide +kernel
end Kernel

private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,7⟩,slots := [],
  body := function.blocks[0]!.body,term := function.blocks[0]!.term }

/-- A real original-source zero divisor after the jump witnesses the complete
instruction-zero class trap theorem. Compiler execution is kernel checked;
only fixed original-input dominance uses the labelled finite native fact. -/
theorem executable_entry_trap_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ = .trapped .intDivz ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        initial.slots ⟨0,0,ρ0,Arm.write_base_gpr 0#5 7 Arm.ArmState.default⟩ (.trapped .intDivz) := by
  have success := compiled
  obtain ⟨result,run⟩ : ∃ result,Stock.lower function = .ok result := by
    cases run : Stock.lower function with
    | error message => rw [run] at success; cases success
    | ok result => exact ⟨result,rfl⟩
  have family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
    have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
      decide +kernel
    intro b member stm present
    exact Stock.Scalar.maskMixedBodyEligible_sound
      (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)
  have quiet : ∀ stm ∈ function.blocks[0]!.body,
      (∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop := by
    intro stm member
    change stm ∈ [⟨[1],.iconst .i64 0⟩,⟨[],.nop⟩] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inl ⟨.i64,0,rfl⟩
    · exact .inr rfl
  have forwarded : ∀ stm ∈ function.blocks[0]!.body,∀ x ∈ stm.results,x ∈ ([1] : List Nat) := by
    intro stm member x defined
    change stm ∈ [⟨[1],.iconst .i64 0⟩,⟨[],.nop⟩] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact defined
    · cases defined
  have entered : Clif.enterFunc function [⟨.i64,7⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ = .trapped .intDivz := rfl
  let world := Arm.write_base_gpr 0#5 7 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩] world := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩)] at member
    have same := List.mem_singleton.mp member
    cases same
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none)
      (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := TwoBlock.entry_trap_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (target := function.blocks[1]!) (bc := ⟨10,[1]⟩) (xs := [3])
    rfl rfl rfl rfl (by decide +kernel) family quiet forwarded (SourceEntry.of_enterFunc entered) trapped
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,scope,dominated,trapped,semantics⟩

end Backend.Stock.Proof.TwoBlockTrapWitness

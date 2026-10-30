import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockEntryScalarFixture
import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.EntryScalarWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000


private def initial (denominator : BitVec 64) : Clif.Frame := {
  func := function,regs := (Clif.Regs.empty.set 0 ⟨.i64,7⟩).set 1 ⟨.i64,denominator⟩,
  slots := [],body := function.blocks[0]!.body,term := function.blocks[0]!.term }
private def world (denominator : BitVec 64) : Arm.ArmState :=
  Arm.write_base_gpr 1#5 denominator (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)

private theorem arguments (denominator : BitVec 64) :
    ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩,⟨.i64,denominator⟩] (world denominator) := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩),(.reg (.x 1),⟨.i64,denominator⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same
  all_goals
    rcases Prod.mk.inj same with ⟨rfl,rfl⟩
    simp [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum,Clif.Ty.width]

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

private theorem entryFamily : ∀ stm ∈ function.blocks[0]!.body,MaskBody.Family stm.inst := by
  intro stm member
  exact family _ (by simp [function]) stm member

private theorem forwarded : ∀ stm ∈ function.blocks[0]!.body,∀ x ∈ stm.results,x ∈ ([200,100] : List Nat) := by
  have all : function.blocks[0]!.body.all (fun stm => stm.results.all ([200,100] : List Nat).contains) = true := by
    decide +kernel
  intro stm member x result
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp all stm member) x result)

private theorem stable : MRStable (fun _ => False) (fun _ _ _ => True) := by
  intro _ _ _ _ _ _; trivial

/-- Instruction-zero ABI entry: (7+3)/3, inherited7 and copied3 return10. -/
theorem executable_entry_scalar_return_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) [] ⟨0,0,ρ0,world 3⟩ (.returned [⟨.i64,10⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,scope,dominated,eligible,domain⟩ := actual_entry_scalar_driver_witness
  have entered : Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,3⟩] Clif.Mem.empty =
      .ok (initial 3,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 3,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,10⟩] Clif.Mem.empty := rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  obtain ⟨ρ0,semantics⟩ := TwoBlock.entry_scalar_return_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (target := function.blocks[1]!) (bc := ⟨10,[200,100]⟩) (xs := [102])
    rfl rfl rfl rfl (by decide +kernel) family entryFamily forwarded (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable (w0 := world 3) trivial (arguments 3)
  exact ⟨result,ρ0,run,semantics⟩

/-- A zero divisor in the entry body traps before the actual jump or successor. -/
theorem executable_entry_scalar_zero_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) [] ⟨0,0,ρ0,world 0⟩ (.trapped .intDivz) := by
  obtain ⟨result,run,scope,dominated,eligible,domain⟩ := actual_entry_scalar_driver_witness
  have entered : Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty =
      .ok (initial 0,Clif.Mem.empty) := rfl
  have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 0,[],Clif.Mem.empty⟩ =
      .trapped .intDivz := rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  obtain ⟨ρ0,semantics⟩ := TwoBlock.entry_scalar_trap_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (target := function.blocks[1]!) (bc := ⟨10,[200,100]⟩) (xs := [102])
    rfl rfl rfl rfl (by decide +kernel) family entryFamily forwarded (SourceEntry.of_enterFunc entered) trapped
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable (w0 := world 0) trivial (arguments 0)
  exact ⟨result,ρ0,run,semantics⟩

end Backend.Stock.Proof.EntryScalarWitness

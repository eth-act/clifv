import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockLinearCfgTrapFixture
import FV.Backend.Proof.StockLinearCfgTrap
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.LinearCfgTrapWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private def initial : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.set 0 ⟨.i64,7⟩).set 1 ⟨.i64,0⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

/-- Actual ABI entry reaches the middle block and traps at its first division.
The final block's demanded result cannot make the trap proof vacuous. -/
theorem executable_three_block_trap_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        initial.slots ⟨0,0,ρ0,Arm.write_base_gpr 1#5 0 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)⟩
        (.trapped .intDivz) := by
  obtain ⟨result,run,scope,dominated,order⟩ := actual_linear_driver_witness
  have entered : Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial,[],Clif.Mem.empty⟩ =
      .trapped .intDivz := rfl
  let initialWorld := Arm.write_base_gpr 1#5 0 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩,⟨.i64,0⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩),(.reg (.x 1),⟨.i64,0⟩)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same <;> cases same
    all_goals
      simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
      rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none)
      (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := LinearCfg.scalar_trap_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (middle := function.blocks[1]!) (target := function.blocks[2]!)
    (first := ⟨10,[]⟩) (second := ⟨20,[]⟩) (xs := [2])
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) family
    (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,scope,dominated,entered,semantics⟩

end Backend.Stock.Proof.LinearCfgTrapWitness

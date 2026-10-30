import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockLinearCfgFixture
import FV.Backend.Proof.StockLinearCfgReturn
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.LinearCfgWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private def initial : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.set 0 ⟨.i64,7⟩).set 1 ⟨.i64,1⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

/-- A real dense source fixture inhabits actual traversal, scan uniqueness,
and both cross-block demand links, with no emitted-shape native fact. -/
theorem actual_demand_transfer_witness : ∃ result es ms ts,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    result.blockScans = #[ts,ms,es] ∧ es.block = 0 ∧ ms.block = 1 ∧ ts.block = 2 ∧
    es.isBranch = true ∧ ms.isBranch = true ∧
    (∀ (x : Nat),ms.output.state.demand[x]! ≤ es.input.demand[x]!) ∧
    (∀ (x : Nat),ts.output.state.demand[x]! ≤ ms.input.demand[x]!) := by
  obtain ⟨result,run,scope,dominated,order⟩ := actual_linear_driver_witness
  obtain ⟨es,ms,ts,events,eb,mb,tb,ebr,mbr,em,mm⟩ := LinearCfg.three_scan_links run scope
    (entry := function.blocks[0]!) (middle := function.blocks[1]!) (target := function.blocks[2]!)
    (first := ⟨10,[]⟩) (second := ⟨20,[]⟩) rfl rfl rfl order
  exact ⟨result,es,ms,ts,run,scope,dominated,events,eb,mb,tb,ebr,mbr,em,mm⟩

/-- Actual ABI entry returns rotate(7,1)=14 through two empty-argument jumps.
The middle result is inherited directly by the final source block. -/
theorem executable_three_block_return_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        initial.slots ⟨0,0,ρ0,Arm.write_base_gpr 1#5 1 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)⟩
        (.returned [⟨.i64,14⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,scope,dominated,order⟩ := actual_linear_driver_witness
  have entered : Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,1⟩] Clif.Mem.empty = .ok (initial,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 7 ⟨initial,[],Clif.Mem.empty⟩ =
      .returned [⟨.i64,14⟩] Clif.Mem.empty := rfl
  let initialWorld := Arm.write_base_gpr 1#5 1 (Arm.write_base_gpr 0#5 7 Arm.ArmState.default)
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,7⟩,⟨.i64,1⟩] initialWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,7⟩),(.reg (.x 1),⟨.i64,1⟩)] at member
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
  obtain ⟨ρ0,semantics⟩ := LinearCfg.scalar_return_frame run scope dominated (by decide +kernel)
    (entry := function.blocks[0]!) (middle := function.blocks[1]!) (target := function.blocks[2]!)
    (first := ⟨10,[]⟩) (second := ⟨20,[]⟩) (xs := [2])
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) family
    (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,scope,dominated,entered,semantics⟩

end Backend.Stock.Proof.LinearCfgWitness

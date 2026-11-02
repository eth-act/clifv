import FV.E2E.StockMemoryTwoBlockPaired
import FV.Backend.Proof.StockMemoryCapturedSource

namespace E2E.StockMemoryCapturedWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.CapturedFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 LoadFixture.world

private theorem memory : LoadFixture.relation.holds function initial.slots LoadFixture.heap world := by
  refine ⟨⟨?_,LoadFixture.memory_world.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact LoadFixture.memory_world.1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments : ArgsAtEntry LoadFixture.relation.F function.sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  rfl


private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem pairedMemory : MRP LoadFixture.relation function 0 (fun _ => True)
    initial.slots LoadFixture.heap (world,otherWorld) := by
  have same : SameWorld (Zof LoadFixture.relation.F (fun _ => True) LoadFixture.heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,LoadFixture.world,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,LoadFixture.world,Arm.ArmState.default]
  · refine ⟨⟨?_,LoadFixture.memory_world.1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact LoadFixture.memory_world.1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,LoadFixture.world,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,LoadFixture.world,Arm.ArmState.default]

/-- Two distinct entry worlds execute the complete captured NOP/jump/load function from PC0.
Only fixed driver acceptance uses the marked native witness; the generic theorem does not. -/
theorem complete_captured_paired_function_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    ∃ result : Result,Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (initial,LoadFixture.heap) ∧
      RunOkABI function result.code
        (pairSem (csem LoadFixture.relation.F ⟨0,0⟩ noExternal))
        (MRP LoadFixture.relation function 0 (fun _ => True)) initial.slots
        ⟨0,0,entrySeed result.ctx initial,(world,otherWorld)⟩
        (.returned [⟨.i32,2779096485⟩] LoadFixture.heap) := by
  refine ⟨by decide +kernel,?_⟩
  have success := lowered
  cases run : Stock.lower function with
  | error err => rw [run] at success; cases success
  | ok result =>
    have registerOnly : ∀ loc ∈ locsOf function.sig,∃ pin,loc = .reg pin := by
      intro loc member
      change loc ∈ [ArgLoc.reg (.x 0)] at member
      exact ⟨.x 0,List.mem_singleton.mp member⟩
    have otherArguments : ArgsAtEntry LoadFixture.relation.F function.sig [⟨.i64,4096⟩] otherWorld := by
      intro loc value member
      change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
      rfl
    have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf function.sig).zip [⟨.i64,4096⟩] → regVal otherWorld pin = regVal world pin := by
      intro pin v member
      change (ArgLoc.reg pin,v) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    have nops : ∀ stm ∈ function.blocks[0]!.body,stm.inst = .nop := by
      intro stm member
      have equal : stm = ⟨[],.nop⟩ := by simpa [function] using member
      subst stm
      rfl
    have shape : ∀ j stm,function.blocks[1]!.body[j]? = some stm → j = 1 ∨ stm.inst = .nop := by
      intro j stm found
      cases j with
      | zero =>
        simp [function] at found
        subst stm
        exact .inr rfl
      | succ j =>
        cases j with
        | zero => exact .inl rfl
        | succ j => simp [function] at found
    have finished := StockMemory.stock_two_block_load_return_paired_function run scope dominated rfl
      (entry := function.blocks[0]!) (target := function.blocks[1]!) rfl nops rfl
      (loadIndex := 1) (x := 0) (z := 2) (flags := LoadFixture.flags) rfl shape rfl
      (by simp [function]) source_entry registerOnly
      (Γ := LoadFixture.relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
      rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
      source_returned pairedMemory arguments otherArguments registers
    exact ⟨result,rfl,source_entered,finished⟩

end E2E.StockMemoryCapturedWitness

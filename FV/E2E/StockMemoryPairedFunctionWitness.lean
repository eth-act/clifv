import FV.E2E.StockMemoryPairedFunction
import FV.Backend.Proof.StockMemorySingleWitness
import FV.Backend.Proof.StockMemoryClass

namespace E2E.StockMemoryFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.SingleFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source conditions positively inhabit the first memory class. -/
theorem source_class_witness : SingleClass function := by
  refine ⟨scope,dominated,rfl,rfl,?_,?_⟩
  · intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  · exact ⟨function.blocks[0]!,0,2,LoadFixture.flags,rfl,rfl,rfl,by simp [function],rfl⟩

private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],
  body := [⟨[2],.load .load .i32 LoadFixture.flags 0 0⟩],term := .ret [2] }
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

/-- Two distinct original ABI-entry worlds execute the actual complete Stock
load/return function from PC0, reading initialized nonzero bytes and sharing one
virtual file throughout. -/
theorem complete_paired_load_function_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (initial,LoadFixture.heap) ∧
      RunOkABI function result.code (pairSem (csem LoadFixture.relation.F ⟨0,0⟩ noExternal))
        (MRP LoadFixture.relation function 0 (fun _ => True)) initial.slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [⟨.i32,2779096485⟩] LoadFixture.heap) := by
  refine ⟨by decide +kernel,?_⟩
  have success := lowered
  cases run : Stock.lower function with
  | error err => rw [run] at success; cases success
  | ok result =>
    have entered : Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap = .ok (initial,LoadFixture.heap) := rfl
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
    obtain ⟨ρ,finished⟩ := StockMemory.single_load_return_paired_function run scope dominated rfl
      (b := function.blocks[0]!) rfl rfl rfl (by simp [function]) (SourceEntry.of_enterFunc entered)
      (show Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],LoadFixture.heap⟩ =
        .returned [⟨.i32,2779096485⟩] LoadFixture.heap from rfl) registerOnly
      (Γ := LoadFixture.relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
      rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
      pairedMemory arguments otherArguments registers
    exact ⟨result,ρ,rfl,entered,finished⟩

end E2E.StockMemoryFunctionWitness

import FV.E2E.StockMemoryExtLoadPairedFunction
import FV.Backend.Proof.StockMemoryExtLoadRecordFixture
import FV.Backend.Proof.StockMemoryExtLoadClass

namespace E2E.StockMemoryExtLoadFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.ExtendedRoots Backend.Stock.Memory.ExtendedRoots.Fixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source conditions positively inhabit the first memory class. -/
theorem source_class_witness (kind : Kind) : Backend.Stock.Memory.ExtendedRoots.SingleClass kind .i64 (function kind) := by
  refine ⟨scope kind,dominated kind,(by cases kind <;> rfl),rfl,?_,?_⟩
  · intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  · exact ⟨(function kind).blocks[0]!,0,2,flags,rfl,rfl,rfl,by simp [function],rfl⟩

private def initial (kind : Kind) : Clif.Frame := {
  func := function kind,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],
  body := [⟨[2],.load kind.sourceOp .i64 flags 0 0⟩],term := .ret [2] }
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def payload : Kind → Nat
  | .unsigned8 => 165 | .signed8 => 2^64-91
  | .unsigned16 => 42405 | .signed16 => 2^64-23131
  | .unsigned32 => 2779096485 | .signed32 => 2^64-1515870811
private def value (kind : Kind) : Clif.Val := Clif.Val.ofNat .i64 (payload kind)
private theorem memory_base (kind : Kind) : relation.holds (function kind) (initial kind).slots heap baseWorld := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have equal : (165 : BitVec 8) = b := Option.some.inj byte
    subst b
    rfl
  · intro a n valid
    have bound : 4096 ≤ a ∧ a+n ≤ 4104 := by
      simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 baseWorld

private theorem memory (kind : Kind) : relation.holds (function kind) (initial kind).slots heap world := by
  refine ⟨⟨?_,(memory_base kind).1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact (memory_base kind).1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments (kind : Kind) : ArgsAtEntry relation.F (function kind).sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  rfl


private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem pairedMemory (kind : Kind) : MRP relation (function kind) 0 (fun _ => True)
    (initial kind).slots heap (world,otherWorld) := by
  have same : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory kind,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]
  · refine ⟨⟨?_,(memory_base kind).1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact (memory_base kind).1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]

/-- Two distinct original ABI-entry worlds execute the actual complete Stock
load/return function from PC0, reading initialized nonzero bytes and sharing one
virtual file throughout. -/
theorem complete_paired_extending_load_function_witness (kind : Kind) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower (function kind) = .ok result ∧
      Clif.enterFunc (function kind) [⟨.i64,4096⟩] heap = .ok (initial kind,heap) ∧
      RunOkABI (function kind) result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation (function kind) 0 (fun _ => True)) (initial kind).slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [value kind] heap) := by
  refine ⟨by decide +kernel,?_⟩
  obtain ⟨input⟩ := record_input kind
  let result := input.result
  have run : Stock.lower (function kind) = .ok result := input.run
  have entered : Clif.enterFunc (function kind) [⟨.i64,4096⟩] heap = .ok (initial kind,heap) := by cases kind <;> rfl
  have registerOnly : ∀ loc ∈ locsOf (function kind).sig,∃ pin,loc = .reg pin := by
    intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  have otherArguments : ArgsAtEntry relation.F (function kind).sig [⟨.i64,4096⟩] otherWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    rfl
  have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf (function kind).sig).zip [⟨.i64,4096⟩] → regVal otherWorld pin = regVal world pin := by
    intro pin v member
    change (ArgLoc.reg pin,v) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
    cases List.mem_singleton.mp member
    simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  obtain ⟨ρ,finished⟩ := StockMemory.ExtendedRoots.single_extending_load_return_paired_function kind .i64 run (scope kind) (dominated kind)
    (by cases kind <;> rfl)
    (b := (function kind).blocks[0]!) rfl rfl rfl (by simp [function]) (SourceEntry.of_enterFunc entered)
    (show Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial kind,[],heap⟩ =
      .returned [value kind] heap from by cases kind <;> rfl) registerOnly
    (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
    rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
    (pairedMemory kind) (arguments kind) otherArguments registers
  exact ⟨result,ρ,run,entered,finished⟩

end E2E.StockMemoryExtLoadFunctionWitness

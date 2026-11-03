import FV.Backend.Proof.StockLinearCfgCompatibility
import FV.E2E.StockMemorySretCopyPairedFunction
import FV.Backend.Proof.StockMemorySretCopyBodyWitness

namespace E2E.StockMemorySretCopyFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.SretCopy.Fixture
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def initial : Clif.Frame := {
  func := function,regs := (Clif.Regs.empty.set 0 ⟨.i64,0⟩).set 1 ⟨.i64,16⟩,slots := [],
  body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩ }
private def bytes (a : Nat) : BitVec 8 := if a = 16 then 37 else if a = 24 then 99 else 0
private def heap : Clif.Mem := {allocs := [⟨0,32,false⟩],bytes := fun a => some (bytes a)}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun a => bytes a.toNat}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def afterHeap : Clif.Mem := (heap.writeBits false 0 8 (37 : BitVec 64)).writeBits false 8 8 (99 : BitVec 64)
private theorem locations : locsOf function.sig = [ArgLoc.reg (.x 8),ArgLoc.reg (.x 0)] := by rw [captured_sret_source_shape_witness]; rfl
private theorem memory_base : relation.holds function initial.slots heap baseWorld := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have bound : a+1 ≤ 32 := by simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    change bytes (a % 2^64) = b
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Option.some.inj byte
  · intro a n valid
    have bound : a+n ≤ 32 := by simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private def world : Arm.ArmState := Arm.write_base_gpr 0#5 16 (Arm.write_base_gpr 8#5 0 baseWorld)

private theorem memory : relation.holds function initial.slots heap world := by
  refine ⟨⟨?_,memory_base.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact memory_base.1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments : ArgsAtEntry relation.F function.sig [⟨.i64,0⟩,⟨.i64,16⟩] world := by
  intro loc val member
  rw [locations] at member
  simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member <;> cases member
  all_goals simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
    Arm.read_store,Arm.write_store,rnum] <;> rfl

private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem pairedMemory : MRP relation function 0 (fun _ => True)
    initial.slots heap (world,otherWorld) := by
  have same : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]
  · refine ⟨⟨?_,memory_base.1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact memory_base.1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]

/-- Distinct entry worlds execute the complete unchanged original sret capture.
Both stored words change. The source signature and implicit x8 return remain intact. -/
theorem complete_paired_sret_copy_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    afterHeap.bytes 0 = some 37 ∧ afterHeap.bytes 8 = some 99 ∧
    heap.bytes 0 = some 0 ∧ heap.bytes 8 = some 0 ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,0⟩,⟨.i64,16⟩] heap = .ok (initial,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 10 ⟨initial,[],heap⟩ = .returned [] afterHeap ∧
      RunOkABIAt function result.code result.edgeArgs (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation function 0 (fun _ => True)) initial.slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [] afterHeap) := by
  refine ⟨by decide +kernel,rfl,rfl,rfl,rfl,?_⟩
  obtain ⟨result,event,run,scope,dominated,abi,events,atMiddle,block,spec⟩ := captured_sret_copy_body_witness
  have entered : Clif.enterFunc function [⟨.i64,0⟩,⟨.i64,16⟩] heap = .ok (initial,heap) := by
    simp only [initial,captured_sret_source_shape_witness]; rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 10 ⟨initial,[],heap⟩ = .returned [] afterHeap := by
    simp only [initial,captured_sret_source_shape_witness]; rfl
  have registerOnly : ∀ loc ∈ locsOf function.sig,∃ pin,loc = .reg pin := by
    intro loc member
    rw [locations] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals exact ⟨_,rfl⟩
  have otherArguments : ArgsAtEntry relation.F function.sig [⟨.i64,0⟩,⟨.i64,16⟩] otherWorld := by
    intro loc val member
    rw [locations] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member | member <;> cases member
    all_goals simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,
      Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum] <;> rfl
  have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈
      (locsOf function.sig).zip [⟨.i64,0⟩,⟨.i64,16⟩] → regVal otherWorld pin = regVal world pin := by
    intro pin v member
    rw [locations] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member | member <;> cases member
    all_goals simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  obtain ⟨ρ,finished⟩ := StockMemory.SretCopy.sret_copy_paired_return_frame run scope dominated abi
    (entry := entry) (middle := middle) (target := exit) (first := ⟨1,[]⟩) (second := ⟨2,[]⟩) (xs := [])
    (by rw [captured_sret_source_shape_witness]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    (by intro stm member; have equal : stm = ⟨[],.nop⟩ := by simpa [entry] using member
        subst stm; rfl)
    (by intro stm member; have equal : stm = ⟨[],.nop⟩ := by simpa [exit] using member
        subst stm; rfl)
    (i0 := 1) (i8 := 2) (j0 := 3) (j8 := 4) (base := 1) (destination := 0) (low := 2) (high := 3)
    rfl rfl rfl rfl (by decide) (by decide)
    (by intro j stm found
        have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
          have bound := lt_of_getElem? found
          change j < 5 at bound
          omega
        rcases indices with rfl | rfl | rfl | rfl | rfl
        all_goals simp [middle] at found; subst stm; simp)
    (by simp [entry]) (by simp [entry]) rfl rfl rfl rfl
    (SourceEntry.of_enterFunc entered) registerOnly returned
    (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
    rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
    pairedMemory arguments otherArguments registers
  exact ⟨result,ρ,run,entered,returned,finished⟩

/-- The complete fixed capture also inhabits the existing compiler function observation. -/
theorem complete_paired_sret_function_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    afterHeap.bytes 0 = some 37 ∧ afterHeap.bytes 8 = some 99 ∧
    heap.bytes 0 = some 0 ∧ heap.bytes 8 = some 0 ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,0⟩,⟨.i64,16⟩] heap = .ok (initial,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 10 ⟨initial,[],heap⟩ = .returned [] afterHeap ∧
      RunOkABI function result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation function 0 (fun _ => True)) initial.slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [] afterHeap) := by
  obtain ⟨distinct,lowWritten,highWritten,lowOld,highOld,result,ρ,run,entered,returned,executed⟩ :=
    complete_paired_sret_copy_witness
  obtain ⟨otherResult,event,otherRun,scope,rest⟩ := captured_sret_copy_body_witness
  have compatible := LinearCfg.legacy_compatible run scope
    (entry := entry) (middle := middle) (target := exit) (first := ⟨1,[]⟩) (second := ⟨2,[]⟩) (xs := [])
    (by rw [captured_sret_source_shape_witness]) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
  exact ⟨distinct,lowWritten,highWritten,lowOld,highOld,result,ρ,run,entered,returned,
    RunOkABIAt.legacyCompatible compatible executed⟩

end E2E.StockMemorySretCopyFunctionWitness

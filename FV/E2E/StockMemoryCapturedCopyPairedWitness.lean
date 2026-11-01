import FV.E2E.StockMemoryCapturedCopyPairedFunction
import FV.Backend.Proof.StockMemoryCapturedCopyWitness

namespace E2E.StockMemoryCapturedCopyFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.CapturedCopy.Fixture
open Backend.Stock.Memory.IntegerRoots.LoadedPointerFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,0⟩,slots := [],
  body := [⟨[],.nop⟩],term := .jump ⟨1,[]⟩ }
private def bytes (a : Nat) : BitVec 8 := if a = 8 then 37 else 0
private def heap : Clif.Mem := {allocs := [⟨0,16,false⟩],bytes := fun a => some (bytes a)}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun a => bytes a.toNat}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def afterHeap : Clif.Mem := heap.writeBits false 0 8 (37 : BitVec 64)
private theorem locations : locsOf function.sig = [ArgLoc.reg (.x 0)] := by rw [captured_source_shape_witness]; rfl
private theorem memory_base : relation.holds function initial.slots heap baseWorld := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have bound : a+1 ≤ 16 := by simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    change bytes (a % 2^64) = b
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Option.some.inj byte
  · intro a n valid
    have bound : a+n ≤ 16 := by simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private def world : Arm.ArmState := Arm.write_base_gpr 0#5 0 baseWorld

private theorem memory : relation.holds function initial.slots heap world := by
  refine ⟨⟨?_,memory_base.1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact memory_base.1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments : ArgsAtEntry relation.F function.sig [⟨.i64,0⟩] world := by
  intro loc val member
  rw [locations] at member
  simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
  cases member
  all_goals simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum] <;> rfl



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

/-- Two distinct ABI-entry worlds execute the complete original captured function.
The loaded pointer aliases the source base, and the store changes its first byte. -/
theorem complete_paired_captured_copy_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    afterHeap.bytes 0 = some 37 ∧ heap.bytes 0 = some 0 ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower function = .ok result ∧
      Clif.enterFunc function [⟨.i64,0⟩] heap = .ok (initial,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 7 ⟨initial,[],heap⟩ = .returned [] afterHeap ∧
      RunOkABI function result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation function 0 (fun _ => True)) initial.slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [] afterHeap) := by
  refine ⟨by decide +kernel,rfl,rfl,?_⟩
  obtain ⟨domain,result,run⟩ := captured_domain_and_lower_witness
  have entered : Clif.enterFunc function [⟨.i64,0⟩] heap = .ok (initial,heap) := by simp only [initial,captured_source_shape_witness]; rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 7 ⟨initial,[],heap⟩ = .returned [] afterHeap := by simp only [initial,captured_source_shape_witness]; rfl
  have registerOnly : ∀ loc ∈ locsOf function.sig,∃ pin,loc = .reg pin := by
    intro loc member
    rw [locations] at member
    exact ⟨_,List.mem_singleton.mp member⟩
  have otherArguments : ArgsAtEntry relation.F function.sig [⟨.i64,0⟩] otherWorld := by
    intro loc val member
    rw [locations] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    cases member
    simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,
      Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    rfl
  have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈
      (locsOf function.sig).zip [⟨.i64,0⟩] → regVal otherWorld pin = regVal world pin := by
    intro pin v member
    rw [locations] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    cases member
    simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  have finished := StockMemory.CapturedCopy.two_block_captured_copy_paired_function
    run domain.scope domain.dominated domain.abi
    (entry := entry) (target := target) (by rw [captured_source_shape_witness])
    (by intro stm member; have equal : stm = ⟨[],.nop⟩ := by simpa [entry] using member
        subst stm; rfl)
    (by rfl) (iv := 1) (ip := 2) (is := 3) (by rfl) (by rfl) (by rfl) (by decide) (by decide)
    (by intro j stm found
        have indices : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
          have bound := lt_of_getElem? found
          change j < 4 at bound
          omega
        rcases indices with rfl | rfl | rfl | rfl
        all_goals simp [target] at found; subst stm; simp)
    (by rfl) (by simp [entry]) (SourceEntry.of_enterFunc entered) registerOnly
    (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
    rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
    returned pairedMemory arguments otherArguments registers
  exact ⟨result,entrySeed result.ctx initial,run,entered,returned,finished⟩

end E2E.StockMemoryCapturedCopyFunctionWitness

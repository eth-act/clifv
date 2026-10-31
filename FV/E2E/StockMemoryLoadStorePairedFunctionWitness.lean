import FV.E2E.StockMemoryLoadStorePairedFunction
import FV.Backend.Proof.StockMemoryLoadStoreCheckWitness

namespace E2E.StockMemoryLoadStoreFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots Backend.Stock.Memory.LoadStore.Fixture
open Backend.Stock.Memory.StoreRoots.Fixture (flags)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def value (kind : Kind) : Clif.Val := Clif.Val.ofNat kind.sourceTy 37
private def initial (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : Clif.Frame := {
  func := function width kind distinct,regs := ((Clif.Regs.empty.set 0 ⟨.i64,4096⟩).set 1 (value kind)).set 2 ⟨.i64,4112⟩,slots := [],
  body := (function width kind distinct).blocks[0]!.body,term := .ret [3] }
private def heap : Clif.Mem := {allocs := [⟨4096,32,false⟩],bytes := fun _ => some 165}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def afterHeap (kind : Kind) (distinct : Bool) : Clif.Mem :=
  heap.writeBits false (if distinct then 4112 else 4096) (kind.sourceOp.size kind.sourceTy) (value kind).bits
private theorem locations (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : locsOf (function width kind distinct).sig = [ArgLoc.reg (.x 0),ArgLoc.reg (.x 1),ArgLoc.reg (.x 2)] := by
  cases width <;> cases kind <;> rfl
private theorem memory_base (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : relation.holds (function width kind distinct) (initial width kind distinct).slots heap baseWorld := by
  refine ⟨⟨?_,?_,rfl⟩,?_,outRel_zero _ _ _⟩
  · intro a b valid byte
    have equal : (165 : BitVec 8) = b := Option.some.inj byte
    subst b
    rfl
  · intro a n valid
    have bound : 4096 ≤ a ∧ a+n ≤ 4128 := by
      simpa [heap,Clif.Mem.valid,Clif.Alloc.contains] using valid
    exact ⟨by omega,fun _ _ h => h⟩
  · intro id b present
    cases present

private def world : Arm.ArmState := Arm.write_base_gpr 2#5 4112 (Arm.write_base_gpr 1#5 37 (Arm.write_base_gpr 0#5 4096 baseWorld))

private theorem memory (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : relation.holds (function width kind distinct) (initial width kind distinct).slots heap world := by
  refine ⟨⟨?_,(memory_base width kind distinct).1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact (memory_base width kind distinct).1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : ArgsAtEntry relation.F (function width kind distinct).sig [⟨.i64,4096⟩,value kind,⟨.i64,4112⟩] world := by
  intro loc val member
  rw [locations width kind distinct] at member
  simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal <;> cases equal
  all_goals cases kind <;> simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum] <;> rfl



private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem pairedMemory (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) : MRP relation (function width kind distinct) 0 (fun _ => True)
    (initial width kind distinct).slots heap (world,otherWorld) := by
  have same : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory width kind distinct,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]
  · refine ⟨⟨?_,(memory_base width kind distinct).1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact (memory_base width kind distinct).1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]

private def loaded : IntegerRoots.Width → Clif.Val
  | .w8 => Clif.Val.ofNat .i8 165
  | .w16 => Clif.Val.ofNat .i16 42405
  | .w32 => Clif.Val.ofNat .i32 2779096485
  | .w64 => Clif.Val.ofNat .i64 11936128518282651045

/-- Complete paired execution returns the pre-store load and preserves the updated heap. -/
theorem complete_paired_load_store_function_witness
    (width : IntegerRoots.Width) (kind : Kind) (distinct : Bool) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    (afterHeap kind distinct).bytes (if distinct then 4112 else 4096) = some 37 ∧
    heap.bytes 4096 = some 165 ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower (function width kind distinct) = .ok result ∧
      Clif.enterFunc (function width kind distinct) [⟨.i64,4096⟩,value kind,⟨.i64,4112⟩] heap =
        .ok (initial width kind distinct,heap) ∧
      RunOkABI (function width kind distinct) result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation (function width kind distinct) 0 (fun _ => True))
        (initial width kind distinct).slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [loaded width] (afterHeap kind distinct)) := by
  refine ⟨by decide +kernel,(by cases kind <;> cases distinct <;> rfl),rfl,?_⟩
  obtain ⟨result,run,checked⟩ := complete_checked_function_witness width kind distinct
  have entered : Clif.enterFunc (function width kind distinct)
      [⟨.i64,4096⟩,value kind,⟨.i64,4112⟩] heap = .ok (initial width kind distinct,heap) := by
    cases width <;> cases kind <;> cases distinct <;> rfl
  have family := source_class_witness width kind distinct
  have otherArguments : ArgsAtEntry relation.F (function width kind distinct).sig
      [⟨.i64,4096⟩,value kind,⟨.i64,4112⟩] otherWorld := by
    intro loc val member
    rw [locations width kind distinct] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal | equal | equal <;> cases equal
    all_goals cases kind <;> simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,
      Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum] <;> rfl
  have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈
      (locsOf (function width kind distinct).sig).zip [⟨.i64,4096⟩,value kind,⟨.i64,4112⟩] →
      regVal otherWorld pin = regVal world pin := by
    intro pin v member
    rw [locations width kind distinct] at member
    simp only [List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal | equal | equal <;> cases equal <;>
      simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
  obtain ⟨ρ,finished⟩ := StockMemory.LoadStore.load_store_return_paired_function width kind kind.sourceTy
    run family.scope family.dominated family.abi
    (b := (function width kind distinct).blocks[0]!) rfl rfl rfl (by simp [function])
    (by cases distinct <;> simp [function]) (valueTy := kind.sourceTy) (by simp [function])
    (by cases kind <;> intro h <;> first | rfl | cases h) (SourceEntry.of_enterFunc entered)
    (show Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial width kind distinct,[],heap⟩ =
      .returned [loaded width] (afterHeap kind distinct) from by
        cases width <;> cases kind <;> cases distinct <;> rfl) family.registers
    (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
    rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
    (pairedMemory width kind distinct) (arguments width kind distinct) otherArguments registers
  exact ⟨result,ρ,run,entered,finished⟩

end E2E.StockMemoryLoadStoreFunctionWitness

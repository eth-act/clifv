import FV.E2E.StockMemoryIntegerPairedFunction
import FV.Backend.Proof.StockMemoryIntegerRecordFixture
import FV.Backend.Proof.StockMemoryIntegerCheck
import FV.Backend.Proof.StockMemoryIntegerClass

namespace E2E.StockMemoryIntegerFunctionWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.IntegerRoots Backend.Stock.Memory.IntegerRoots.Fixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original source conditions positively inhabit the first memory class. -/
theorem source_class_witness (width : Width) : Backend.Stock.Memory.IntegerRoots.SingleClass width (function width) := by
  refine ⟨scope width,dominated width,(by cases width <;> rfl),rfl,?_,?_⟩
  · intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  · exact ⟨(function width).blocks[0]!,0,2,flags,rfl,rfl,rfl,by simp [function],rfl⟩

/-- Reflection of an existing dominance proof avoids kernel execution of the
hash-based availability algorithm. This helper changes no input condition. -/
private theorem dominatedB_of_facts {f : Clif.Function}
    (unique : nodupB (valueDefs f) = true) (dominated : Dominated f) : dominatedB f = true := by
  simp only [dominatedB,unique,Bool.true_and]
  cases built : Backend.buildCtx f with
  | error message => rfl
  | ok output =>
    obtain ⟨ctx,ranges,st⟩ := output
    simp only
    apply List.all_eq_true.mpr
    intro bi member
    cases block : f.blocks[bi]? with
    | none => simp only [block]
    | some b =>
      simp only [block,Bool.and_eq_true,List.all_eq_true]
      have facts := ctxFacts_of built
      have defs : DefsAt ctx b (startOnly (blockStart f bi)).start := fun k stm atStatement r contains =>
        (facts.defs dominated.ssa r _).mpr ⟨bi,b,k,stm,block,atStatement,contains,rfl⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro j member
        cases statement : b.body[j]? with
        | none => simp only [statement]
        | some stm =>
          simp only [statement,List.all_eq_true]
          intro y contains
          exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).1 j stm statement y contains)
      · intro y contains
        exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).2 y contains)
      · intro x available
        simp only [Bool.or_eq_true,Std.HashSet.contains_ofList,List.contains_iff_mem,
          List.all_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
        by_cases isLocal : x ∈ defsOf f bi
        · exact .inl isLocal
        · exact .inr (dominated.paramFree _ _ _ built bi x available isLocal)

/-- Each additional width positively inhabits the executable source classifier. -/
theorem checked_source_class_witness (width : Width) (additional : width ≠ .w32) :
    ∃ chosen,Backend.Stock.Memory.IntegerRoots.SingleClass chosen (function width) := by
  have accepted : Stock.MemoryUnsigned.sourceOk (function width) = true := by
    simp only [Stock.MemoryUnsigned.sourceOk,Bool.and_eq_true,Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,(source_class_witness width).abi⟩,
      (source_class_witness width).ordinary⟩,rfl⟩
    · cases width <;> simp_all [Stock.MemoryUnsigned.eligible,function,Width.sourceTy,flags]
    · cases width <;> decide +kernel
    · apply dominatedB_of_facts ?_ (dominated width)
      change nodupB [0,2] = true
      simp [nodupB]
  exact Stock.MemoryUnsigned.sourceOk_sound accepted

private def initial (width : Width) : Clif.Frame := {
  func := function width,regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩,slots := [],
  body := [⟨[2],.load .load width.sourceTy flags 0 0⟩],term := .ret [2] }
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def payload : Width → Nat
  | .w8 => 165 | .w16 => 42405 | .w32 => 2779096485 | .w64 => 11936128518282651045
private def value (width : Width) : Clif.Val := Clif.Val.ofNat width.sourceTy (payload width)
private theorem memory_base (width : Width) : relation.holds (function width) (initial width).slots heap baseWorld := by
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

private theorem memory (width : Width) : relation.holds (function width) (initial width).slots heap world := by
  refine ⟨⟨?_,(memory_base width).1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact (memory_base width).1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments (width : Width) : ArgsAtEntry relation.F (function width).sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  rfl


private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem pairedMemory (width : Width) : MRP relation (function width) 0 (fun _ => True)
    (initial width).slots heap (world,otherWorld) := by
  have same : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory width,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]
  · refine ⟨⟨?_,(memory_base width).1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact (memory_base width).1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,baseWorld,Arm.write_base_gpr,Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]

/-- Two distinct original ABI-entry worlds execute the actual complete Stock
load/return function from PC0, reading initialized nonzero bytes and sharing one
virtual file throughout. -/
theorem complete_paired_integer_load_function_witness (width : Width) :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower (function width) = .ok result ∧
      Clif.enterFunc (function width) [⟨.i64,4096⟩] heap = .ok (initial width,heap) ∧
      RunOkABI (function width) result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation (function width) 0 (fun _ => True)) (initial width).slots ⟨0,0,ρ,(world,otherWorld)⟩
        (.returned [value width] heap) := by
  refine ⟨by decide +kernel,?_⟩
  obtain ⟨input⟩ := record_input width
  let result := input.result
  have run : Stock.lower (function width) = .ok result := input.run
  have entered : Clif.enterFunc (function width) [⟨.i64,4096⟩] heap = .ok (initial width,heap) := by cases width <;> rfl
  have registerOnly : ∀ loc ∈ locsOf (function width).sig,∃ pin,loc = .reg pin := by
    intro loc member
    change loc ∈ [ArgLoc.reg (.x 0)] at member
    exact ⟨.x 0,List.mem_singleton.mp member⟩
  have otherArguments : ArgsAtEntry relation.F (function width).sig [⟨.i64,4096⟩] otherWorld := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
    rfl
  have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈ (locsOf (function width).sig).zip [⟨.i64,4096⟩] → regVal otherWorld pin = regVal world pin := by
    intro pin v member
    change (ArgLoc.reg pin,v) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
    cases List.mem_singleton.mp member
    simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,Arm.write_store,rnum]
  obtain ⟨ρ,finished⟩ := StockMemory.IntegerRoots.single_integer_load_return_paired_function width run (scope width) (dominated width)
    (by cases width <;> rfl)
    (b := (function width).blocks[0]!) rfl rfl rfl (by simp [function]) (SourceEntry.of_enterFunc entered)
    (show Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial width,[],heap⟩ =
      .returned [value width] heap from by cases width <;> rfl) registerOnly
    (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
    rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
    (pairedMemory width) (arguments width) otherArguments registers
  exact ⟨result,ρ,run,entered,finished⟩

end E2E.StockMemoryIntegerFunctionWitness

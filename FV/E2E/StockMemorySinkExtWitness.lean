import FV.E2E.StockMemorySinkExtNI
import FV.E2E.StockMemoryExplicitWorldX
import FV.E2E.LinkArm
import FV.Backend.Proof.LowerDecide

/-! Non-vacuity of the sinking class, its explicit-trap contract, the trap exclusion
and the paired execution, on Cranelift's `load-extends.clif` functions
`%load_uextend_i8_i32` and `%load_sextend_i16_i64` with their default (trapping)
loads. The signed function runs end to end on bytes `0xA5`, so its sign extension
produces a negative value. Rule 810's class runs end to end on `atomic_load.clif`'s
`%atomic_load_i32_i64`: the actual code's one acquiring load returns `0xA5A5A5A5`. -/
namespace E2E.StockMemory.SinkExtendWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.SinkExtend E2E.StockMemory.SinkExtend
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.lower

private def sourceBlock (src : Source) (kind : Kind) (out : Clif.Ty) : Clif.Block :=
  { id := 0, params := [(0,.i64)],
    body := [⟨[1],src.load (loadTy kind) {} 0⟩,⟨[2],.extend (extendOp kind) out 1⟩],
    term := .ret [2] }

private def sourceFunction (src : Source) (kind : Kind) (out : Clif.Ty) : Clif.Function :=
  { name := "load_extend",
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨out,.none,.normal⟩] },
    blocks := [sourceBlock src kind out] }

private abbrev block (kind : Kind) (out : Clif.Ty) : Clif.Block := sourceBlock .plain kind out
private abbrev function (kind : Kind) (out : Clif.Ty) : Clif.Function := sourceFunction .plain kind out

private def lowers (kind : Kind) (out : Clif.Ty) : Bool :=
  match Stock.lower (function kind out) with
  | .ok _ => true
  | .error _ => false

private def acquireLowers : Bool :=
  match Stock.lower (sourceFunction .acquire .unsigned32 .i64) with
  | .ok _ => true
  | .error _ => false

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.lower
private theorem lowers_uextend : lowers .unsigned8 .i32 = true := by decide +kernel
private theorem lowers_sextend : lowers .signed16 .i64 = true := by decide +kernel
private theorem scope_uextend : lowerScopeB (function .unsigned8 .i32) = true := by decide +kernel
private theorem scope_sextend : lowerScopeB (function .signed16 .i64) = true := by decide +kernel
private theorem lowers_acquire : acquireLowers = true := by decide +kernel
private theorem scope_acquire : lowerScopeB (sourceFunction .acquire .unsigned32 .i64) = true := by
  decide +kernel
end Kernel

private theorem sourceDominated (src : Source) (kind : Kind) (out : Clif.Ty) :
    Dominated (sourceFunction src kind out) := by
  constructor
  · change ([0,1,2] : List Nat).Nodup; decide
  · intro ctx ranges st build bi b found
    have bound : bi < 1 := by have h := lt_of_getElem? found; simpa [sourceFunction] using h
    have zero : bi = 0 := by omega
    subst bi
    simp [sourceFunction] at found
    subst b
    constructor
    · intro j stm present
      cases j with
      | zero =>
        simp [sourceBlock] at present
        subst stm
        intro x member
        have zero : x = 0 := by cases src <;> simpa [Source.load,Driver.instArgs] using member
        subst x
        simp [availOf,sourceFunction,sourceBlock,defsBefore,defsFrom]
      | succ j =>
        cases j with
        | zero =>
          simp [sourceBlock] at present
          subst stm
          intro x member
          have one : x = 1 := by simpa [Driver.instArgs] using member
          subst x
          simp [availOf,sourceFunction,sourceBlock,defsBefore,defsFrom]
        | succ j => simp [sourceBlock] at present
    · intro x member
      have two : x = 2 := by
        simpa [abiTerm,Driver.termArgs,sretRet,sigRets,sourceFunction,sourceBlock] using member
      subst x
      simp [availOf,sourceFunction,sourceBlock,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := sourceFunction src kind out) (ctx := ctx) (gn := id)).cand tl x
      available
    have length : (sourceFunction src kind out).blocks.length = 1 := rfl
    omega

private theorem dominated (kind : Kind) (out : Clif.Ty) : Dominated (function kind out) :=
  sourceDominated .plain kind out

private theorem class_of (kind : Kind) (out : Clif.Ty) (small : narrow out = true)
    (scope : lowerScopeB (function kind out) = true) (abi : sigAbiOk (function kind out).sig = true) :
    SinkExtClass kind out (function kind out) := by
  refine ⟨lowerScope_of scope,dominated kind out,abi,by simp [sourceFunction,sigRets],?_,
    ⟨block kind out,0,1,2,{},rfl,rfl,rfl,small,by simp [sourceBlock],by simp [sourceFunction,sigRets]⟩⟩
  intro loc member
  change loc ∈ [ArgLoc.reg (.x 0)] at member
  exact ⟨.x 0,List.mem_singleton.mp member⟩

/-- Both filetest functions inhabit the source class and its explicit-trap contract. -/
theorem sink_extend_class_witness :
    SinkExtClass .unsigned8 .i32 (function .unsigned8 .i32) ∧
      SinkExtClass .signed16 .i64 (function .signed16 .i64) ∧
      ExplicitDomain (function .unsigned8 .i32) ∧ ExplicitDomain (function .signed16 .i64) := by
  have unsignedClass := class_of .unsigned8 .i32 rfl scope_uextend rfl
  have signedClass := class_of .signed16 .i64 rfl scope_sextend rfl
  exact ⟨unsignedClass,signedClass,unsignedClass.domain,signedClass.domain⟩

private def sourceInitial (src : Source) (kind : Kind) (out : Clif.Ty) : Clif.Frame :=
  { func := sourceFunction src kind out, regs := Clif.Regs.empty.set 0 ⟨.i64,4096⟩, slots := [],
    body := (sourceBlock src kind out).body, term := (sourceBlock src kind out).term }
private abbrev initial (kind : Kind) (out : Clif.Ty) : Clif.Frame := sourceInitial .plain kind out
private def heap : Clif.Mem := {allocs := [⟨4096,8,false⟩],bytes := fun _ => some 165}
private def program : Clif.Program := {funcs := []}

/-- The explicit-trap premise holds on a real returning run (byte `0xA5` at 4096), and the
trap exclusion applies to it: the load could trap at another address, but not under
`TrapsExplicit`. -/
theorem sink_extend_no_trap_witness :
    Clif.runLoop Clif.Env.empty program.bare 3 ⟨initial .unsigned8 .i32,[],heap⟩ =
      .returned [⟨.i32,165⟩] heap ∧
    TrapsExplicit Clif.Env.empty program.bare ⟨initial .unsigned8 .i32,[],heap⟩ ∧
    ∀ fuel code,Clif.runLoop Clif.Env.empty program.bare fuel ⟨initial .unsigned8 .i32,[],heap⟩ ≠
      .trapped code := by
  have returned : Clif.runLoop Clif.Env.empty program.bare 3 ⟨initial .unsigned8 .i32,[],heap⟩ =
      .returned [⟨.i32,165⟩] heap := by rfl
  have explicit := trapsExplicit_of_returned returned
  obtain ⟨b,x,y,z,flags,shape⟩ := (class_of .unsigned8 .i32 rfl scope_uextend rfl).shape
  have sameBlock : b = block .unsigned8 .i32 := by
    have h := shape.blocks
    simp only [function,sourceFunction,List.cons.injEq,and_true] at h
    exact h.symm
  subst sameBlock
  exact ⟨returned,explicit,fun fuel code =>
    stock_sink_extend_no_trap .unsigned8 shape rfl rfl explicit fuel code⟩

private def baseWorld : Arm.ArmState := {Arm.ArmState.default with mem := fun _ => 165}
private def world : Arm.ArmState := Arm.write_base_gpr 0#5 4096 baseWorld
private def otherWorld : Arm.ArmState := Arm.write_base_gpr 10#5 17 world
private def relation : E2E.Rel := ⟨fun _ => False,fun _ => none,0,0⟩
private def noExternal : ExtSem := ⟨fun _ _ _ => none,fun _ _ => 0,0,fun _ _ => Arm.PState.zero⟩

private theorem memory_base (g : Clif.Function) : relation.holds g [] heap baseWorld := by
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

private theorem memory (g : Clif.Function) : relation.holds g [] heap world := by
  refine ⟨⟨?_,(memory_base g).1.valid,rfl⟩,?_,E2E.outRel_zero _ _ _⟩
  · intro a b valid byte; exact (memory_base g).1.bytes a b valid byte
  · intro id b present; cases present

private theorem arguments (src : Source) (kind : Kind) (out : Clif.Ty) :
    ArgsAtEntry relation.F (sourceFunction src kind out).sig [⟨.i64,4096⟩] world := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
  cases List.mem_singleton.mp member
  simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,
    Arm.write_store,rnum]
  rfl

private theorem pairedMemory (g : Clif.Function) :
    MRP relation g 0 (fun _ => True) [] heap (world,otherWorld) := by
  have same : SameWorld (Zof relation.F (fun _ => True) heap) world otherWorld := by
    simpa only [otherWorld,Arm.w] using (SameWorld.refl _ world).w_right
      (f := .GPR 10#5) (v := 17) (by change (10 < 29 ∧ 10 ≠ 18) ∨ 10 = 30; decide)
  refine ⟨⟨memory g,?_,?_⟩,⟨?_,?_,?_⟩,same⟩
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,world,baseWorld,Arm.write_base_gpr,Arm.write_store,
      Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,world,Arm.write_base_gpr,baseWorld,Arm.ArmState.default]
  · refine ⟨⟨?_,(memory_base g).1.valid,rfl⟩,?_,outRel_zero _ _ _⟩
    · intro a b valid byte; exact (memory_base g).1.bytes a b valid byte
    · intro id b present; cases present
  · simp [spv,Arm.r,Arm.read_base_gpr,Arm.read_store,otherWorld,world,baseWorld,Arm.write_base_gpr,
      Arm.write_store,Arm.ArmState.default]
  · simp only [Arm.r,Arm.read_base_error,otherWorld,world,Arm.write_base_gpr,baseWorld,
      Arm.ArmState.default]

/-- `%load_sextend_i16_i64` end to end in paired worlds: two distinct ABI-entry worlds run
the actual Stock code (one `sload16`) from instruction zero, read the initialized bytes
`0xA5A5` and return the sign-extended negative value `0xFFFFFFFFFFFFA5A5`. -/
theorem complete_paired_sink_extend_function_witness :
    Arm.r (.GPR 10#5) otherWorld ≠ Arm.r (.GPR 10#5) world ∧
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower (function .signed16 .i64) = .ok result ∧
      Clif.enterFunc (function .signed16 .i64) [⟨.i64,4096⟩] heap = .ok (initial .signed16 .i64,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial .signed16 .i64,[],heap⟩ =
        .returned [⟨.i64,2^64-23131⟩] heap ∧
      RunOkABI (function .signed16 .i64) result.code (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation (function .signed16 .i64) 0 (fun _ => True)) (initial .signed16 .i64).slots
        ⟨0,0,ρ,(world,otherWorld)⟩ (.returned [⟨.i64,2^64-23131⟩] heap) := by
  refine ⟨by decide +kernel,?_⟩
  have lowered := lowers_sextend
  unfold lowers at lowered
  cases run : Stock.lower (function .signed16 .i64) with
  | error e => rw [run] at lowered; cases lowered
  | ok result =>
    have family := class_of .signed16 .i64 rfl scope_sextend rfl
    obtain ⟨b,x,y,z,flags,shape⟩ := family.shape
    have entered : Clif.enterFunc (function .signed16 .i64) [⟨.i64,4096⟩] heap =
        .ok (initial .signed16 .i64,heap) := by rfl
    have returned : Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨initial .signed16 .i64,[],heap⟩ =
        .returned [⟨.i64,2^64-23131⟩] heap := by rfl
    have otherArguments : ArgsAtEntry relation.F (function .signed16 .i64).sig [⟨.i64,4096⟩] otherWorld := by
      intro loc value member
      change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
      rfl
    have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈
        (locsOf (function .signed16 .i64).sig).zip [⟨.i64,4096⟩] → regVal otherWorld pin = regVal world pin := by
      intro pin v member
      change (ArgLoc.reg pin,v) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,
        Arm.write_store,rnum]
    have finished := sink_extend_return_paired_function_seeded .signed16 run family.scope family.dominated
      family.abi shape (SourceEntry.of_enterFunc entered) returned family.registers
      (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
      rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
      (pairedMemory _) (arguments .plain .signed16 .i64) otherArguments registers
    exact ⟨result,_,rfl,entered,returned,finished⟩

private theorem acquire_class :
    SourceExtClass .acquire .unsigned32 .i64 (sourceFunction .acquire .unsigned32 .i64) := by
  refine ⟨lowerScope_of scope_acquire,sourceDominated .acquire .unsigned32 .i64,rfl,
    by simp [sourceFunction,sigRets],?_,
    ⟨sourceBlock .acquire .unsigned32 .i64,0,1,2,{},rfl,rfl,rfl,rfl,by simp [sourceBlock],
      by simp [sourceFunction,sigRets],rfl⟩⟩
  intro loc member
  change loc ∈ [ArgLoc.reg (.x 0)] at member
  exact ⟨.x 0,List.mem_singleton.mp member⟩

/-- `%atomic_load_i32_i64` inhabits the atomic source class and its explicit-trap contract;
the explicit-trap premise holds on its real returning run, and under it the run never
traps. -/
theorem acquire_extend_class_witness :
    SourceExtClass .acquire .unsigned32 .i64 (sourceFunction .acquire .unsigned32 .i64) ∧
      ExplicitDomain (sourceFunction .acquire .unsigned32 .i64) ∧
      Clif.runLoop Clif.Env.empty program.bare 3 ⟨sourceInitial .acquire .unsigned32 .i64,[],heap⟩ =
        .returned [⟨.i64,2779096485⟩] heap ∧
      ∀ fuel code,Clif.runLoop Clif.Env.empty program.bare fuel
        ⟨sourceInitial .acquire .unsigned32 .i64,[],heap⟩ ≠ .trapped code := by
  have returned : Clif.runLoop Clif.Env.empty program.bare 3
      ⟨sourceInitial .acquire .unsigned32 .i64,[],heap⟩ = .returned [⟨.i64,2779096485⟩] heap := by rfl
  have explicit := trapsExplicit_of_returned returned
  obtain ⟨b,x,y,z,flags,shape⟩ := acquire_class.shape
  have sameBlock : b = sourceBlock .acquire .unsigned32 .i64 := by
    have h := shape.blocks
    simp only [sourceFunction,List.cons.injEq,and_true] at h
    exact h.symm
  subst sameBlock
  exact ⟨acquire_class,acquire_class.domain,returned,fun fuel code =>
    stock_source_extend_no_trap .acquire .unsigned32 shape rfl rfl explicit fuel code⟩

/-- `%atomic_load_i32_i64` end to end in paired worlds: two distinct ABI-entry worlds run
the actual rule-810 code (one 32-bit acquiring load) from instruction zero, read the
initialized bytes and return the zero-extended value `0xA5A5A5A5`. -/
theorem complete_paired_acquire_extend_function_witness :
    ∃ (result : Result) (ρ : Nat → CV),Stock.lower (sourceFunction .acquire .unsigned32 .i64) = .ok result ∧
      Clif.enterFunc (sourceFunction .acquire .unsigned32 .i64) [⟨.i64,4096⟩] heap =
        .ok (sourceInitial .acquire .unsigned32 .i64,heap) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨sourceInitial .acquire .unsigned32 .i64,[],heap⟩ =
        .returned [⟨.i64,2779096485⟩] heap ∧
      RunOkABI (sourceFunction .acquire .unsigned32 .i64) result.code
        (pairSem (csem relation.F ⟨0,0⟩ noExternal))
        (MRP relation (sourceFunction .acquire .unsigned32 .i64) 0 (fun _ => True))
        (sourceInitial .acquire .unsigned32 .i64).slots
        ⟨0,0,ρ,(world,otherWorld)⟩ (.returned [⟨.i64,2779096485⟩] heap) := by
  have lowered := lowers_acquire
  unfold acquireLowers at lowered
  cases run : Stock.lower (sourceFunction .acquire .unsigned32 .i64) with
  | error e => rw [run] at lowered; cases lowered
  | ok result =>
    have family := acquire_class
    obtain ⟨b,x,y,z,flags,shape⟩ := family.shape
    have entered : Clif.enterFunc (sourceFunction .acquire .unsigned32 .i64) [⟨.i64,4096⟩] heap =
        .ok (sourceInitial .acquire .unsigned32 .i64,heap) := by rfl
    have returned : Clif.runLoop Clif.Env.empty {funcs := []} 3
        ⟨sourceInitial .acquire .unsigned32 .i64,[],heap⟩ = .returned [⟨.i64,2779096485⟩] heap := by rfl
    have otherArguments : ArgsAtEntry relation.F (sourceFunction .acquire .unsigned32 .i64).sig
        [⟨.i64,4096⟩] otherWorld := by
      intro loc value member
      change (loc,value) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp only [VHolds,regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
        Arm.read_store,Arm.write_store,rnum]
      rfl
    have registers : ∀ (pin : Reg) (v : Clif.Val),(.reg pin,v) ∈
        (locsOf (sourceFunction .acquire .unsigned32 .i64).sig).zip [⟨.i64,4096⟩] →
          regVal otherWorld pin = regVal world pin := by
      intro pin v member
      change (ArgLoc.reg pin,v) ∈ [(.reg (.x 0),⟨.i64,4096⟩)] at member
      cases List.mem_singleton.mp member
      simp [regVal,otherWorld,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,Arm.read_store,
        Arm.write_store,rnum]
    have finished := source_extend_return_paired_function_seeded .acquire .unsigned32 run family.scope
      family.dominated family.abi shape (SourceEntry.of_enterFunc entered) returned family.registers
      (Γ := relation) (c := 0) (D := fun _ => True) (fc := ⟨0,0⟩) (X := noExternal)
      rfl (fun _ _ h => by cases h) (by intro Z n w w' subset same; rfl)
      (pairedMemory _) (arguments .acquire .unsigned32 .i64) otherArguments registers
    exact ⟨result,_,rfl,entered,returned,finished⟩

end E2E.StockMemory.SinkExtendWitness

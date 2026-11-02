import FV.Backend.Proof.StockLoopBounded
import FV.Backend.Proof.StockParameterEntry
import FV.Backend.Proof.StockParameterWitness
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockConditionalEmptyFixture
import FV.Backend.Proof.StockConditionalEmptyTrapFixture
import FV.Backend.Proof.StockCfgReturnBlockAt
import FV.Backend.Proof.StockCfgReturnTrapAt
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

/-! Non-vacuity of the fuel-bounded block compositions (#140, T7b-2). The kernel-checked
parameter fixtures (an entry jump with arguments into a parameter branch) and the empty
conditional fixtures meet every premise; each successor continuation is the bounded
restriction of the forward one at the fuel of the actual source run. -/

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

/-- `parameter_jump_return_frame` through `jump_body_returns_below`. -/
private theorem jump_return_below {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump refines driver stable env cp
  obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
    CriticalOwners.jump_successor run scope tag source jump
  have sameTarget : spec.target = targetLabel := by
    have row : result.order.successors[0]! = #[targetLabel] := by simp only [getElem!_def,successors,Option.getD_some]
    have targets := spec.targets
    rw [row] at targets
    exact (List.cons.inj targets).1.symm
  obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
  obtain ⟨next,nextEvent,nextBlock,nextReturns⟩ := nonentry_parameter_returns run scope dominated abi ranked terms family refines driver stable
    env cp targetTag targetSource targetNonentry
  obtain ⟨table,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have edge : tl ∈ table[0]!.toList := by rw [jump_source_row computed source jump targetIndex]; simp
  have demand := successor_demand run scope ranked computed
    (by simpa only [spec.atBlock] using tag)
    (by simpa only [nextBlock] using targetTag)
    (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have below := nextReturns.below fuel
  have continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp left s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro left smaller s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using below left smaller s vals outMem ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_returns_below run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- `parameter_jump_trap_frame` through `jump_body_traps_below`. -/
private theorem jump_trap_below {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (jump : entry.term = .jump bc)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr) {fuel : Nat} {code : Clif.TrapCode}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.trapped code) := by
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag source jump refines driver stable env cp
  obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
    CriticalOwners.jump_successor run scope tag source jump
  have sameTarget : spec.target = targetLabel := by
    have row : result.order.successors[0]! = #[targetLabel] := by simp only [getElem!_def,successors,Option.getD_some]
    have targets := spec.targets
    rw [row] at targets
    exact (List.cons.inj targets).1.symm
  obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
  obtain ⟨next,nextEvent,nextBlock,nextTraps⟩ := nonentry_parameter_traps run scope dominated abi ranked terms family refines driver stable
    env cp targetTag targetSource targetNonentry
  obtain ⟨table,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have edge : tl ∈ table[0]!.toList := by rw [jump_source_row computed source jump targetIndex]; simp
  have demand := successor_demand run scope ranked computed
    (by simpa only [spec.atBlock] using tag)
    (by simpa only [nextBlock] using targetTag)
    (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
  have remaining : fr.body = entry.body := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.body frame
  have atTerm : fr.term = entry.term := by
    obtain ⟨b,regs,found,types,paramTypes,set,frame⟩ := entered
    have found' : f.blocks[0]? = some b := by simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using found
    cases Option.some.inj (found'.symm.trans source)
    exact congrArg Clif.Frame.term frame
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated spec
    entered driver memorySem stable memory arguments
  have below := nextTraps.below fuel
  have continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp left s = .trapped code →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
    intro left smaller s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using below left smaller s code ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_traps_below run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- The entry jump with arguments and the parameter branch return through the bounded jump
composition from ABI entry. -/
theorem jump_body_returns_below_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial 1).slots ⟨0,0,ρ0,Arm.write_base_gpr 0#5 1 Arm.ArmState.default⟩
        (.returned [⟨.i64,1⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,_,_⟩ := lowered
  obtain ⟨entered,returned,_⟩ := source_cases
  let world := Arm.write_base_gpr 0#5 1 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,1⟩] world := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,1⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := jump_return_below run scope dominated rfl ranked nonentry_terms family
    (entry := function.blocks[0]!) rfl rfl (SourceEntry.of_enterFunc entered) returned
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,semantics⟩

/-- The all-fuel continuation of the actual parameter branch block is recovered from its
bounded restrictions. -/
theorem returns_below_recovers_witness (X : ExtSem) :
    ∃ result event,Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      ReturnsAt function result 1 1 function.blocks[1]! event
        (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []} := by
  obtain ⟨result,event,run,member,atBlock,returns⟩ := actual_return_continuation_witness X
  exact ⟨result,event,run,member,atBlock,
    returnsAt_of_below fun bound => (returns.below (bound+1)).mono (Nat.le_succ bound)⟩

namespace Trap
/-- The entry jump with arguments, the parameter branch and the division by zero trap
through the bounded jump composition from ABI entry. -/
theorem jump_body_traps_below_witness (X : ExtSem) :
    ∃ result ρ0,Stock.lower function = .ok result ∧
      RunOkABIAt function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True)
        (initial 0).slots ⟨0,0,ρ0,Arm.write_base_gpr 0#5 0 Arm.ArmState.default⟩ (.trapped .intDivz) := by
  obtain ⟨result,run,_,_⟩ := lowered
  have entered : Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial 0,Clif.Mem.empty) := rfl
  have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz := rfl
  let world := Arm.write_base_gpr 0#5 0 Arm.ArmState.default
  have arguments : ArgsAtEntry (fun _ => False) function.sig [⟨.i64,0⟩] world := by
    intro loc value member
    change (loc,value) ∈ [(.reg (.x 0),⟨.i64,0⟩)] at member
    cases List.mem_singleton.mp member
    simp only [VHolds,regVal,world,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ0,semantics⟩ := jump_trap_below run scope dominated rfl ranked nonentry_terms family
    (entry := function.blocks[0]!) rfl rfl (SourceEntry.of_enterFunc entered) trapped
    (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
    memorySem stable trivial arguments
  exact ⟨result,ρ0,run,semantics⟩

/-- The all-fuel trap continuation of the actual parameter branch block is recovered from its
bounded restrictions. -/
theorem traps_below_recovers_witness (X : ExtSem) :
    ∃ result event,Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 1 ∧
      TrapsAt function result 1 1 function.blocks[1]! event
        (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []} := by
  obtain ⟨result,event,run,member,atBlock,traps⟩ := actual_trap_continuation_witness X
  exact ⟨result,event,run,member,atBlock,
    trapsAt_of_below fun bound => (traps.below (bound+1)).mono (Nat.le_succ bound)⟩
end Trap

end Backend.Stock.Proof.ParameterCfg.Fixture

namespace Backend.Stock.Proof.ConditionalValues.BelowWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem family : ∀ b ∈ EmptyFixture.function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have checked : EmptyFixture.function.blocks.all
      (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp checked b member) stm present)

private theorem trapFamily : ∀ b ∈ EmptyTrapFixture.function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have checked : EmptyTrapFixture.function.blocks.all
      (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp checked b member) stm present)

/-- The empty conditional fixture returns through the bounded conditional composition from
its actual entry seed; both successor continuations are bounded below the run's fuel 3. -/
theorem returning_empty_parameter_below_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec EmptyFixture.function result EmptyFixture.function.blocks[0]! 0 0 7
      ⟨1,[]⟩ ⟨2,[]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower EmptyFixture.function = .ok result ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨EmptyFixture.initial,[],Clif.Mem.empty⟩ =
        .returned [⟨.i64,1⟩] Clif.Mem.empty ∧
      RunOkABIAt EmptyFixture.function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) EmptyFixture.initial.slots
        ⟨0,spec.preludeCode.size,entrySeed spec.core.scan.ctx EmptyFixture.initial,Arm.ArmState.default⟩
        (.returned [⟨.i64,1⟩] Clif.Mem.empty) := by
  obtain ⟨result,run,scope,dominated,entered,returned⟩ := EmptyFixture.driver_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have refines := refines_csem (fun _ => False) ⟨0,0⟩ X
  have driver := driverSem_csem (fun _ => False) ⟨0,0⟩ X
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
    (b := EmptyFixture.function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[]⟩) (no := ⟨2,[]⟩) rfl
    refines driver stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx EmptyFixture.function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx EmptyFixture.function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have ordered : blockOrder EmptyFixture.function =
      .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have abi : sigAbiOk EmptyFixture.function.sig = true := rfl
  have successors : ∀ (index : Nat) (bc : Clif.BlockCall),
      (dests EmptyFixture.function.blocks[0]!.term)[index]? = some bc →
      Nonempty (SuccessorReturn EmptyFixture.function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) Clif.Env.empty {funcs := []} [⟨.i64,1⟩] Clif.Mem.empty) := by
    intro index bc selected
    cases index with
    | zero =>
      change some ⟨1,[]⟩ = some bc at selected
      cases Option.some.inj selected
      exact SuccessorReturn.of_return_block run scope dominated abi family refines driver stable
        (tl := 1) (targetLabel := 2) (b := EmptyFixture.function.blocks[1]!)
        rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
    | succ index =>
      cases index with
      | zero =>
        change some ⟨2,[]⟩ = some bc at selected
        cases Option.some.inj selected
        exact SuccessorReturn.of_return_block run scope dominated abi family refines driver stable
          (tl := 2) (targetLabel := 1) (b := EmptyFixture.function.blocks[2]!)
          rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
      | succ index => cases selected
  have defined : SourceDefinedAt EmptyFixture.function result.ctx spec.core.scan.block 0 EmptyFixture.initial := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  exact ⟨result,spec,run,returned,spec.returning_empty_parameter_below run scope dominated family
    refines driver stable tag rfl parameter conditionTy ⟨rfl,rfl⟩ (successor_returns_below successors 3)
    rfl rfl rfl defined returned held⟩

/-- The empty trap fixture traps through the bounded conditional composition from its actual
entry seed; both successor continuations are bounded below the run's fuel 4. -/
theorem trapping_empty_parameter_below_witness (X : ExtSem) :
    ∃ result, ∃ (spec : ConditionalBodySpec EmptyTrapFixture.function result EmptyTrapFixture.function.blocks[0]!
      0 0 7 ⟨1,[]⟩ ⟨2,[]⟩ (csem (fun _ => False) ⟨0,0⟩ X)
      (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower EmptyTrapFixture.function = .ok result ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨EmptyTrapFixture.initial,[],Clif.Mem.empty⟩ =
        .trapped .intDivz ∧
      RunOkABIAt EmptyTrapFixture.function result.code result.edgeArgs (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) EmptyTrapFixture.initial.slots
        ⟨0,spec.preludeCode.size,entrySeed spec.core.scan.ctx EmptyTrapFixture.initial,Arm.ArmState.default⟩
        (.trapped .intDivz) := by
  obtain ⟨result,run,scope,dominated,entered,returned⟩ := EmptyTrapFixture.driver_witness
  have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have refines := refines_csem (fun _ => False) ⟨0,0⟩ X
  have driver := driverSem_csem (fun _ => False) ⟨0,0⟩ X
  obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated trapFamily tag
    (b := EmptyTrapFixture.function.blocks[0]!) rfl (c := 7) (yes := ⟨1,[]⟩) (no := ⟨2,[]⟩) rfl
    refines driver stable Clif.Env.empty {funcs := []}
  let built := (Stock.buildCtx EmptyTrapFixture.function).toOption.getD (sinkCtx,#[],sinkState)
  have build : Stock.buildCtx EmptyTrapFixture.function = .ok built := rfl
  have context : result.ctx = built.1 := congrArg Prod.fst (Except.ok.inj (spec.build.symm.trans build))
  have parameter : result.ctx.defInst? 7 = none := by rw [context]; rfl
  have conditionTy : result.ctx.valueType? 7 = some (.int 32) ∨ result.ctx.valueType? 7 = some (.int 64) := by
    right
    rw [context]
    rfl
  have ordered : blockOrder EmptyTrapFixture.function =
      .ok ⟨#[.original 0,.original 2,.original 1],#[#[2,1],#[],#[]]⟩ := by cbv
  have orderEq := Except.ok.inj ((stock_lower_order run).symm.trans ordered)
  have abi : sigAbiOk EmptyTrapFixture.function.sig = true := rfl
  have successors : ∀ (index : Nat) (bc : Clif.BlockCall),
      (dests EmptyTrapFixture.function.blocks[0]!.term)[index]? = some bc →
      Nonempty (SuccessorTrap EmptyTrapFixture.function result 0 bc (csem (fun _ => False) ⟨0,0⟩ X)
        (fun _ _ _ => True) Clif.Env.empty {funcs := []} .intDivz) := by
    intro index bc selected
    cases index with
    | zero =>
      change some ⟨1,[]⟩ = some bc at selected
      cases Option.some.inj selected
      exact SuccessorTrap.of_return_block run scope dominated abi trapFamily refines driver stable
        (tl := 1) (targetLabel := 2) (b := EmptyTrapFixture.function.blocks[1]!)
        rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
    | succ index =>
      cases index with
      | zero =>
        change some ⟨2,[]⟩ = some bc at selected
        cases Option.some.inj selected
        exact SuccessorTrap.of_return_block run scope dominated abi trapFamily refines driver stable
          (tl := 2) (targetLabel := 1) (b := EmptyTrapFixture.function.blocks[2]!)
          rfl rfl rfl (by rw [orderEq]; rfl) rfl (by decide) (by decide)
      | succ index => cases selected
  have defined : SourceDefinedAt EmptyTrapFixture.function result.ctx spec.core.scan.block 0
      EmptyTrapFixture.initial := by
    rw [spec.atBlock]
    exact source_defined_enterFunc dominated result.ctx entered
  have held := stock_lower_entered_seed_guarded run scope dominated spec.events entered
    spec.core.scan.output.state (MR := fun _ _ _ => True) Arm.ArmState.default trivial
  exact ⟨result,spec,run,returned,spec.trapping_empty_parameter_below run scope dominated trapFamily
    refines driver stable tag rfl parameter conditionTy ⟨rfl,rfl⟩ (successor_traps_below successors 4)
    rfl rfl rfl defined returned held⟩

end Backend.Stock.Proof.ConditionalValues.BelowWitness

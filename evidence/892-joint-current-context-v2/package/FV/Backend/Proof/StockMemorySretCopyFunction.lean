import FV.Backend.Proof.StockLinearCfgShape
import FV.Backend.Proof.StockLinearCfgDemand
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.StockMemoryNopJumpSource
import FV.Backend.Proof.StockMemoryNopNonentryReturn
import FV.Backend.Proof.StockMemoryOrdinaryCfgJumpReturnAt
import FV.Backend.Proof.StockMemorySretCopyJumpSpec
import FV.Backend.Proof.StockMemorySretCopyBodySplit

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Proof.LinearCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem assemble_nonentry_code {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (nonentry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.insts = code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  simp only [show (bi == 0) = false from by simp [nonentry],Bool.false_eq_true,ite_false] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

private theorem nonentry_prelude {f : Clif.Function} {result : Result} {b : Clif.Block}
    {label bi : Nat} {bc : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp) (nonentry : bi ≠ 0) :
    spec.preludeCode.size = 0 := by
  have code := assemble_nonentry_code nonentry spec.assembled
  have sizes := congrArg Array.size (spec.rawCode.symm.trans code)
  simp only [Array.size_append] at sizes
  omega

/-- Instruction-zero simulation of the original three-block memory copy, including
inherited source values across empty-argument jumps. The source signature retains its original implicit sret return. -/
theorem sret_copy_return_frame_canonical {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry middle target : Clif.Block}
    {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id)
    (entryNops : ∀ stm ∈ entry.body,stm.inst = .nop)
    (targetNops : ∀ stm ∈ target.body,stm.inst = .nop)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : middle.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : middle.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : middle.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : middle.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,middle.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    (baseParameter : base ∈ entry.params.map (·.1))
    (destinationParameter : destination ∈ entry.params.map (·.1))
    (loadLowNotrap : lf0.trapCode = none) (loadHighNotrap : lf8.trapCode = none)
    (storeLowNotrap : sf0.trapCode = none) (storeHighNotrap : sf8.trapCode = none)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,entrySeed result.ctx fr,w0⟩ (.returned vals outMem) := by
  have source : f.blocks[0]? = some entry := by simp [blocks]
  have middleSource : f.blocks[1]? = some middle := by simp [blocks]
  have targetSource : f.blocks[2]? = some target := by simp [blocks]
  have order : result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩ :=
    Except.ok.inj ((stock_lower_order run).symm.trans (block_order_three blocks firstJump secondJump ret
      firstDestination secondDestination entryMiddle entryTarget middleTarget))
  have entryTag : result.order.nodes[0]? = some (.original 0) := by simp [order]
  have middleTag : result.order.nodes[1]? = some (.original 1) := by simp [order]
  have targetTag : result.order.nodes[2]? = some (.original 2) := by simp [order]
  obtain ⟨es⟩ := Control.stock_lower_nop_jump_body_spec run scope dominated entryTag source entryNops firstJump
    driver (MR := MR) env cp
  obtain ⟨ms⟩ := captured_sret_copy_jump_spec run scope dominated middleTag middleSource
    loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape source baseParameter destinationParameter
    secondJump loadLowNotrap loadHighNotrap storeLowNotrap storeHighNotrap driver stable memorySem memoryOk env cp
  obtain ⟨targetRanges,targetParams,targetInput,targetData,targetCore,targetRaw,targetPrelude,
    targetCoreRun,targetAssembled,targetBuild,targetSizes,targetPrepared,targetEvents,targetAtBlock,
    targetRawCode,targetPlaced⟩ := stock_lower_original_block_scan_assembly run targetTag
  have et : es.target = 1 := by
    have targets := es.targets
    rw [order] at targets
    exact (List.cons.inj targets).1.symm
  have mt : ms.target = 2 := by
    have targets := ms.targets
    rw [order] at targets
    exact (List.cons.inj targets).1.symm
  have firstIndex : blockIdx? f first.block = some 1 := by
    simp [blockIdx?,blocks,firstDestination,List.findIdx?_cons,entryMiddle,Ne.symm entryMiddle]
  have secondIndex : blockIdx? f second.block = some 2 := by
    simp [blockIdx?,blocks,secondDestination,List.findIdx?_cons,entryTarget,Ne.symm entryTarget,middleTarget,Ne.symm middleTarget]
  have middleFound : f.block? first.block = some middle := by
    simp [Clif.Function.block?,blocks,firstDestination,entryMiddle,Ne.symm entryMiddle]
  have targetFound : f.block? second.block = some target := by
    simp [Clif.Function.block?,blocks,secondDestination,entryTarget,Ne.symm entryTarget,middleTarget,Ne.symm middleTarget]
  have mm := jump_successor_demand run scope blocks firstJump secondJump order ms.events targetEvents
    (Or.inr ⟨ms.atBlock,targetAtBlock⟩) ms.split
  have middleFamily : ∀ stm ∈ middle.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    rcases shape j stm found with selected | selected | selected | selected | nop
    · subst j
      have same := Option.some.inj (found.symm.trans loadLow)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans loadHigh)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans storeLow)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · subst j
      have same := Option.some.inj (found.symm.trans storeHigh)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · simp [OrdinaryBody.OrdinaryInst,nop]
  have targetReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = target.body → s.frame.term = target.term →
      SourceDefinedAt f result.ctx 2 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result targetCore.scan.ctx targetCore.scan.block MR targetCore.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
          ⟨ms.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := Backend.Stock.Memory.actual_nonentry_nop_return run scope dominated abi targetTag targetSource
      (by decide) targetEvents targetAtBlock targetNops ret refines stable func callers remaining atTerm
      (by simpa only [targetAtBlock] using defined) returned held
    simpa only [mt] using finished
  have middleReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = middle.body → s.frame.term = middle.term →
      SourceDefinedAt f result.ctx 1 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result ms.core.scan.ctx ms.core.scan.block MR ms.core.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
          ⟨es.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := Control.ordinary_jump_body_returns_at_of_body run scope dominated refines driver stable ms middleFamily
      (by
        intro a a' steps ρ w relation
        obtain ⟨ρ',w',executed,post⟩ := captured_sret_copy_body_of_split run scope dominated ms.events ms.split.block
          loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape source baseParameter destinationParameter
          stable memorySem memoryOk ms.split a a'
          (by simpa only [sourceBodyIndices,List.reverse_reverse] using steps) ρ w
          (by simpa only [ms.split.state] using relation.1)
        exact ⟨ρ',w',executed,post,by intro x impossible; cases impossible⟩)
      middleTag secondJump (by simpa only [mt] using targetTag) secondIndex targetFound
      targetEvents targetAtBlock mm targetReturns callers remaining atTerm
      (by simpa only [ms.atBlock] using defined) returned held
    simpa only [et,nonentry_prelude ms (by decide)] using finished
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
  obtain ⟨ρentry,wentry,path,guarded,allValues,sameWorld⟩ := Control.jump_entry_prelude run scope dominated
    es entered driver memorySem stable memory arguments
  have finished := Control.nop_jump_body_returns_at run scope dominated refines driver stable es entryNops entryTag firstJump
    (by simpa only [et] using middleTag) firstIndex middleFound ms.events ms.atBlock (by rw [et]; decide) middleReturns
    rfl remaining atTerm
    (by simpa only [es.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  have seed : entrySeed es.core.scan.ctx fr = entrySeed result.ctx fr := by
    classical
    let make (lookup : Nat → Option Reg) (key : Nat) : CV :=
      if h : ∃ pair : Nat × Clif.Val,
          lookup pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 then
        (Classical.choose h).2.bits.setWidth 128
      else 0
    change make es.core.scan.ctx.valueReg? = make result.ctx.valueReg?
    rw [funext (stock_lower_record_context run scope es.events).2.1]
  rw [← seed]
  exact RunOkABIAt.prefix path finished


/-- Preserve the existing existential seed variant. -/
theorem sret_copy_return_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {entry middle target : Clif.Block}
    {first second : Clif.BlockCall} {xs : List Nat}
    (blocks : f.blocks = [entry,middle,target])
    (firstJump : entry.term = .jump first) (secondJump : middle.term = .jump second)
    (ret : target.term = .ret xs)
    (firstDestination : first.block = middle.id) (secondDestination : second.block = target.id)
    (entryMiddle : entry.id ≠ middle.id) (entryTarget : entry.id ≠ target.id)
    (middleTarget : middle.id ≠ target.id)
    (entryNops : ∀ stm ∈ entry.body,stm.inst = .nop)
    (targetNops : ∀ stm ∈ target.body,stm.inst = .nop)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : middle.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : middle.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : middle.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : middle.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,middle.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    (baseParameter : base ∈ entry.params.map (·.1))
    (destinationParameter : destination ∈ entry.params.map (·.1))
    (loadLowNotrap : lf0.trapCode = none) (loadHighNotrap : lf8.trapCode = none)
    (storeLowNotrap : sf0.trapCode = none) (storeHighNotrap : sf8.trapCode = none)
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (memoryOk : MemRelOk F sb syms f MR)
    {w0 : Arm.ArmState} (memory : MR fr.slots cm w0) (arguments : ArgsAtEntry F f.sig args w0) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs isem MR fr.slots ⟨0,0,ρ0,w0⟩ (.returned vals outMem) := by
  exact ⟨entrySeed result.ctx fr,sret_copy_return_frame_canonical run scope dominated abi
    blocks firstJump secondJump ret firstDestination secondDestination entryMiddle entryTarget middleTarget
    entryNops targetNops loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape
    baseParameter destinationParameter loadLowNotrap loadHighNotrap storeLowNotrap storeHighNotrap
    entered returned refines driver memorySem stable memoryOk memory arguments⟩

end Backend.Stock.Memory.SretCopy

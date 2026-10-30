import FV.Backend.Proof.StockParameterReturn
import FV.Backend.Proof.StockParameterTrap
import FV.Backend.Proof.StockJumpEntryPrelude

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Instruction-zero ABI return simulation for any ranked scalar jump/return
source graph whose entry jumps onward. All blocks may have ordinary bodies and
inherited source values; no fixed chain length or forwarding premise is used. -/
theorem parameter_jump_return_frame {f : Clif.Function} {result : Result} {rank : Nat → Nat}
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
  have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using nextReturns fuel s vals outMem ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_returns_at run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

/-- Instruction-zero ABI first-trap simulation for any ranked scalar jump/return
source graph whose entry jumps onward. All blocks may have ordinary bodies and
inherited source values; no fixed chain length or forwarding premise is used. -/
theorem parameter_jump_trap_frame {f : Clif.Function} {result : Result} {rank : Nat → Nat}
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
  have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
      SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    simpa only [sameTarget] using nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
  have finished := Control.jump_body_traps_at run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
    rfl remaining atTerm
    (by simpa only [spec.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

end Backend.Stock.Proof.ParameterCfg

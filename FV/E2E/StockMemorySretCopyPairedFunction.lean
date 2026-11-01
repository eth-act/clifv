import FV.E2E.StockMemoryOrdinaryPairedJump
import FV.E2E.StockMemorySretCopyPairedBodySplit
import FV.E2E.StockMemoryNopNonentryPairedReturn
import FV.E2E.StockMemoryPairedNopJump
import FV.E2E.StockMemoryOriginalEntryPaired
import FV.Backend.Proof.StockLinearCfgShape
import FV.Backend.Proof.StockLinearCfgDemand
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.StockMemoryNopJumpSource
import FV.Backend.Proof.StockMemoryNopNonentryReturn
import FV.Backend.Proof.StockMemoryOrdinaryCfgJumpReturnAt
import FV.Backend.Proof.StockMemorySretCopyJumpSpec
import FV.Backend.Proof.StockMemorySretCopyBodySplit

namespace E2E.StockMemory.SretCopy
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.SretCopy
open Backend.Stock.Proof.LinearCfg Backend.Stock.Proof.Control
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
theorem sret_copy_paired_return_frame {f : Clif.Function} {result : Result}
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
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {fuel : Nat} {vals : List Clif.Val} {outMem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals outMem)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w0 w1 : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w0,w1))
    (arguments : ArgsAtEntry Γ.F f.sig args w0) (otherArguments : ArgsAtEntry Γ.F f.sig args w1)
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w1 pin = regVal w0 pin) :
    ∃ ρ0,RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots ⟨0,0,ρ0,(w0,w1)⟩ (.returned vals outMem) := by
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
    (driverSem_csem Γ.F fc X) (MR := RelW Γ f c) env cp
  obtain ⟨ms⟩ := captured_sret_copy_jump_spec run scope dominated middleTag middleSource
    loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape source baseParameter destinationParameter
    secondJump loadLowNotrap loadHighNotrap storeLowNotrap storeHighNotrap
    (driverSem_csem Γ.F fc X) (mrStable_relW Γ f c) (memRefines_csem Γ.F fc X slot symbols)
    (memRelOk_relW Γ f c) env cp
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
  have targetReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : W2),
      s.frame.func = f → s.callers = [] → s.frame.body = target.body → s.frame.term = target.term →
      SourceDefinedAt f result.ctx 2 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      PairedScanRel f result targetCore.scan.ctx targetCore.scan.block Γ c D targetCore.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D) s.frame.slots
          ⟨ms.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := actual_nonentry_paired_nop_return (fc := fc) run scope dominated abi targetTag targetSource
      (by decide) targetEvents targetAtBlock targetNops ret tls func callers remaining atTerm
      (by simpa only [targetAtBlock] using defined) returned held
    simpa only [mt] using finished
  have middleReturns : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : W2),
      s.frame.func = f → s.callers = [] → s.frame.body = middle.body → s.frame.term = middle.term →
      SourceDefinedAt f result.ctx 1 0 s.frame → Clif.runLoop env cp fuel s = .returned vals outMem →
      PairedScanRel f result ms.core.scan.ctx ms.core.scan.block Γ c D ms.core.scan.output.state
        (0,s.frame,s.mem) ρ w → RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D) s.frame.slots
          ⟨es.target,0,ρ,w⟩ (.returned vals outMem) := by
    intro fuel s ρ w func callers remaining atTerm defined returned held
    have finished := ordinary_paired_jump_body_returns_at_of_body run scope dominated ms middleFamily
      (by
        intro a a' steps ρ w relation
        obtain ⟨ρ',w',executed,post⟩ := captured_sret_copy_paired_body_of_split run scope dominated ms.events ms.split.block
          loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape source baseParameter destinationParameter
          slot symbols tls ms.split a a'
          (by simpa only [sourceBodyIndices,List.reverse_reverse] using steps) ρ w
          (by simpa only [ms.split.state] using relation)
        exact ⟨ρ',w',executed,post⟩)
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
  have nonempty : 0 < es.core.code.size := by
    rw [es.bodyCode]
    simp only [Array.size_append,Array.size_singleton]
    omega
  let entryCore : EntryCoreSpec f result entry := {
    ranges := es.ranges
    params := es.params
    core := es.core
    raw := es.raw
    preludeCode := es.preludeCode
    build := es.build
    sizes := es.sizes
    assembled := es.assembled
    events := es.events
    block := source
    rawCode := es.rawCode
    placed := es.placed
    nonempty := nonempty }
  obtain ⟨ρentry,path,guarded⟩ := original_entry_prelude_paired run scope dominated entryCore entered
    registerOnly slot symbols memory arguments otherArguments registers
  have finished := paired_nop_jump_body_returns_at run scope dominated es entryNops entryTag firstJump
    (by simpa only [et] using middleTag) firstIndex middleFound ms.events ms.atBlock (by rw [et]; decide) middleReturns
    rfl remaining atTerm
    (by simpa only [es.atBlock] using Control.source_defined_entry_frame dominated result.ctx entered)
    returned guarded
  exact ⟨entrySeed es.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

end E2E.StockMemory.SretCopy

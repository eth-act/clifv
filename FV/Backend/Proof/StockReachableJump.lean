import FV.Backend.Proof.StockReachableReturn
import FV.Backend.Proof.StockInheritedJumpDefined
import FV.Backend.Proof.StockMemorySourceExecution
import FV.Backend.Proof.StockCfgSuccessorDemand
import FV.Backend.Proof.StockMemoryOrdinaryJumpDefined
import FV.Backend.Proof.StockCfgDemandValues
import FV.Backend.Proof.StockCfgReturnBlockAt
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.StockComputedCfg
import FV.Backend.Proof.StockMemoryCfgJumpReturnAt
import FV.Backend.Proof.StockMemoryNopBodySource
import FV.Backend.Proof.StockCfgTraversalDemand
import FV.Backend.Proof.StockMemoryNopBody
import FV.Backend.Proof.StockMemoryCfgReturnRefinesAt
import FV.Backend.Proof.StockCfgReturnBlock
import FV.Backend.Proof.StockCfgTraversalScans
import FV.Backend.Proof.StockLinearCfgShape
import FV.Backend.Proof.StockLinearCfgDemand
import FV.Backend.Proof.StockJumpEntryPrelude
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.StockMemoryNopJumpSource
import FV.Backend.Proof.StockMemoryNopNonentryReturn
import FV.Backend.Proof.StockMemoryOrdinaryCfgJumpReturnAt
import FV.Backend.Proof.StockMemorySretCopyJumpSpec
import FV.Backend.Proof.StockMemorySretCopyBodySplit
namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Compose a proved ordinary body and the actual jump while preserving source definedness. -/
theorem ordinary_jump_carry_returns_reachable_of_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc)
    (localFamily : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    (bodyRefines : ∀ a a',SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (sourceBodyIndices f spec.core.scan.block b).reverse a a' → ∀ ρ w,
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.body.state a ρ w → ∃ ρ' w',
        seqRun isem (spec.body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
              spec.term.output.state a' ρ' w')
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals cm ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      (∀ x,needed x → t.frame.regs x = s.frame.regs x) ∧ t.frame.term = .jump bc ∧
      seqRun isem (spec.core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) ρ' w' ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧ Reach env cp s t := by
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := OrdinaryBody.actual_ordinary_source_execution_frame
    run spec.events spec.split localFamily (j := 0) (by omega) (by simpa using remaining) returned
  have path := ordinary_source_steps_reach run spec.events spec.split localFamily
    (fun i member => by
      have bounds := List.mem_range'.mp member
      let j := i-blockStart f spec.core.scan.block
      have inside : j < b.body.length := by dsimp [j]; omega
      exact ⟨j,b.body[j],List.getElem?_eq_getElem inside,by dsimp [j]; omega⟩) steps s.callers
  have sourceReach : Reach env cp s t := by
    change Reach env cp ⟨s.frame,s.callers,s.mem⟩ ⟨t.frame,t.callers,t.mem⟩
    rw [frame.1]
    exact path
  obtain ⟨ρ',w',bodyRun,post⟩ := bodyRefines (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ w (by simpa only [spec.split.state] using held)
  obtain ⟨sourceFrame,atJump,executed,tDefined⟩ := jump_continuation_defined run scope dominated driver spec jump
    available (by simpa only [Nat.add_zero,Nat.sub_zero] using steps) frame atTerm bodyRun defined
  exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined,sourceReach⟩


end Backend.Stock.Proof.Inherited
namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Compose an independently proved actual jump body with a source-correct continuation at
its successor. Only successor-demanded values cross the machine edge. -/
theorem ordinary_jump_body_reachable_at_of_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (localFamily : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst)
    (bodyRefines : ∀ a a',SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (sourceBodyIndices f spec.core.scan.block b).reverse a a' → ∀ ρ w,
      Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (fun _ => False)
        spec.body.state a ρ w → ∃ ρ' w',
        seqRun isem (spec.body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧
        Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (fun _ => False)
          spec.term.output.state a' ρ' w')
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {vals : List Clif.Val} {outMem : Clif.Mem} {retIds : List Nat}
    (continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      ReturnFromAt env cp f result.code result.edgeArgs isem MR s retIds
        ⟨spec.target,0,ρ,w⟩ (.returned vals outMem))
    {fuel : Nat} {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w) :
    ReturnFromAt env cp f result.code result.edgeArgs isem MR s retIds
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨t,left,ρ',w',total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined,sourceReach⟩ :=
    Inherited.ordinary_jump_carry_returns_reachable_of_body run scope dominated refines driver stable spec jump
      localFamily (needed := fun _ => False) (by intro x h; cases h) bodyRefines remaining atTerm returned
      ⟨held,by intro x h; cases h⟩ defined
  cases left with
  | zero => cases continued
  | succ left =>
    have crossing : ∃ fr',Clif.enterBlock t.frame bc = .ok fr' := by
      cases call : Clif.enterBlock t.frame bc with
      | ok fr' => exact ⟨fr',rfl⟩
      | trap code =>
        rw [Clif.runLoop_succ] at continued
        simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
        cases continued
      | stuck message =>
        rw [Clif.runLoop_succ] at continued
        simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
        cases continued
    obtain ⟨fr',crossed⟩ := crossing
    have successor : result.order.successors[label]![0]? = some spec.target := by
      have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
      rw [targets]; rfl
    obtain ⟨ρnext,copied,nextDefined,nextHeld⟩ := direct_successor_guarded_of_demand run scope dominated
      spec.events nextEvent tag source (by simp [jump,dests]) successor targetTag targetIndex target
      spec.atBlock nextBlock post.1 (by simpa only [spec.atBlock] using tDefined) crossed
      (jump_successor_values_of_demand run scope dominated spec jump targetTag targetIndex target nextBlock demand post.1)
    have nextReturned : Clif.runLoop env cp left ⟨fr',[],t.mem⟩ = .returned vals outMem := by
      rw [Clif.runLoop_succ] at continued
      have tc : t.callers = [] := frame.1.trans callers
      simpa only [Clif.step,empty,atJump,Clif.stepTerm,crossed,Clif.StepResult.ofRes,tc] using continued
    have tFunc := post.1.1
    obtain ⟨destination,args,regs,found,read,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = targetBlock := by
      rw [tFunc] at found
      exact Option.some.inj (found.symm.trans target)
    have bodyEq : fr'.body = targetBlock.body := by rw [frEq,destinationEq]
    have termEq : fr'.term = targetBlock.term := by rw [frEq,destinationEq]
    have slotsEq : fr'.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := continuation left ⟨fr',[],t.mem⟩ ρnext w' nextHeld.1 rfl bodyEq termEq
      nextDefined nextReturned nextHeld
    let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
    have segment : SegAt {spec.raw with
        insts := spec.raw.insts.map (·.mapRegs resolve)
        params := spec.raw.params.map resolve
        branchArgs := spec.raw.branchArgs.map resolve}
        spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
      intro k hk
      have bound : k < spec.core.code.size := by simpa using hk
      simp only [spec.rawCode,Array.map_append]
      rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
      simp only [Array.size_map,Nat.add_sub_cancel_left]
      simp [bound]
    have last : spec.preludeCode.size+spec.body.code.size+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append,Array.size_singleton]
      omega
    obtain ⟨ps,cfg⟩ := stock_lower_computed_cfg run scope
    have actualSuccessor : succOf result.code label 0 = some spec.target := by
      cases row : result.order.successors[label]? with
      | none =>
        simp only [getElem!_def,row,Option.getD_none] at successor
        change (#[] : Array Nat)[0]? = some spec.target at successor
        cases successor
      | some values => simpa [succOf,cfg,getElem!_def,row] using successor
    have path := seqRun_goto_starAt spec.placed segment executed last actualSuccessor
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left] using copied)
    have step : Clif.step env cp t = .next ⟨fr',[],t.mem⟩ := by
      rw [Clif.step_term env cp t empty,atJump]
      simp only [Clif.stepTerm,crossed,Clif.StepResult.ofRes,frame.1,callers]
    have connected := ReturnFromAt.source_prefix (sourceReach.snoc step) slotsEq finished
    exact ReturnFromAt.prefix path connected

end Backend.Stock.Proof.Control
namespace Backend.Stock.Proof.Control
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original NOP syntax supplies the guarded body required by the actual jump.
The successor can contain memory instructions. No body-execution certificate is an input. -/
theorem nop_jump_body_reachable_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    (forward : label < spec.target)
    {vals : List Clif.Val} {outMem : Clif.Mem} {retIds : List Nat}
    (continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      ReturnFromAt env cp f result.code result.edgeArgs isem MR s retIds
        ⟨spec.target,0,ρ,w⟩ (.returned vals outMem))
    {fuel : Nat} {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w) :
    ReturnFromAt env cp f result.code result.edgeArgs isem MR s retIds
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  have localFamily : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    simp [OrdinaryBody.OrdinaryInst,nops stm member]
  have demand := CfgDemand.ordered_scan_demand_of_labels run scope
    (Array.getElem?_eq_some_iff.mp targetTag).1 forward
    (by simp only [getElem!_def,targetTag,Option.getD_some,nextBlock])
    (by simp only [getElem!_def,tag,Option.getD_some,spec.atBlock]) nextEvent spec.events spec.split
  apply ordinary_jump_body_reachable_at_of_body run scope dominated refines driver stable spec localFamily
    ?_ tag jump targetTag targetIndex target nextEvent nextBlock demand continuation
    callers remaining atTerm defined returned held
  intro a a' steps ρ w relation
  obtain ⟨ρ',w',executed,post⟩ := Backend.Stock.Memory.stock_nop_body_of_split run scope dominated
    spec.events spec.split.block nops spec.split a a'
    (by simpa only [sourceBodyIndices,List.reverse_reverse] using steps) ρ w
    (by simpa only [spec.split.state] using relation.1)
  exact ⟨ρ',w',executed,post,by intro x impossible; cases impossible⟩

end Backend.Stock.Proof.Control

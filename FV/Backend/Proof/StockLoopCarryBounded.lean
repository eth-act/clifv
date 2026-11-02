import FV.Backend.Proof.StockLoopCarry

/-! Fuel-bounded block compositions with carry sets (#140, T7b-3).

`StockLoopBounded` composes one block with its successor continuations below the block's fuel,
but it keeps the forward premises (`forward`, the demand order). Here a block holds
`CarryRel` of its carry set at entry, and each successor continuation needs `CarryRel` of the
successor's carry set; `EdgeCover` replaces the forward premises, so the successor may be a loop
header entered by a back edge. With empty carry sets and forward edges the compositions are the
ones of `StockLoopBounded` (`successor_returns_carry_below`, `successor_traps_carry_below`). -/

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `jump_body_returns_below` with carry sets in place of the demand premise. -/
theorem jump_body_carry_returns_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    {carry carried : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    (carriedAvailable : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) tl 0)
    (cover : EdgeCover f result tl (targetBlock.params.map (·.1)) next.output.state carried
      spec.term.output.state carry)
    {vals : List Clif.Val} {outMem : Clif.Mem} {fuel : Nat}
    (continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp left s = .returned vals outMem →
      Inherited.CarryRel f result next.ctx next.block MR carried next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.returned vals outMem))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨t,left,ρ',w',total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩ :=
    Inherited.scalar_jump_carry_returns_defined run scope dominated refines driver stable spec jump formats
      (family b (List.mem_of_getElem? source)) available remaining atTerm returned held defined
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
    obtain ⟨ρnext,copied,nextDefined,nextHeld⟩ := jump_successor_carry run scope dominated spec tag jump
      targetTag targetIndex target nextEvent nextBlock carriedAvailable cover post
      (by simpa only [spec.atBlock] using tDefined) crossed
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
    have finished := continuation left (by omega) ⟨fr',[],t.mem⟩ ρnext w' nextHeld.1.1 rfl bodyEq termEq
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
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotsEq] using whole

/-- `jump_body_traps_below` with carry sets in place of the demand premise. -/
theorem jump_body_carry_traps_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    {carry carried : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    (carriedAvailable : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) tl 0)
    (cover : EdgeCover f result tl (targetBlock.params.map (·.1)) next.output.state carried
      spec.term.output.state carry)
    {code : Clif.TrapCode} {fuel : Nat}
    (continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp left s = .trapped code →
      Inherited.CarryRel f result next.ctx next.block MR carried next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.trapped code))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.trapped code) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
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
  have carried' :=
    Inherited.scalar_jump_carry_traps_or_continues_defined run scope dominated refines driver stable spec jump formats
      (family b (List.mem_of_getElem? source)) available remaining atTerm returned held defined
  rcases carried' with failed | continuedBody
  · obtain ⟨offset,i,ops,ρ',w',outs,final,execution,coded⟩ := failed
    obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    exact ⟨label,spec.preludeCode.size+offset,ρ',w',_,i,ops,outs,final,path,spec.placed,
      inst,operands,semantics,coded⟩
  · obtain ⟨t,left,ρ',w',total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩ := continuedBody
    cases left with
    | zero => cases continued
    | succ left =>
      have crossing : ∃ fr',Clif.enterBlock t.frame bc = .ok fr' := by
        cases call : Clif.enterBlock t.frame bc with
        | ok fr' => exact ⟨fr',rfl⟩
        | trap code => exact False.elim (enterBlock_ne_trap call)
        | stuck message =>
          rw [Clif.runLoop_succ] at continued
          simp only [Clif.step,empty,atJump,Clif.stepTerm,call,Clif.StepResult.ofRes] at continued
          cases continued
      obtain ⟨fr',crossed⟩ := crossing
      have successor : result.order.successors[label]![0]? = some spec.target := by
        have targets : result.order.successors[label]! = #[spec.target] := Array.toList_inj.mp spec.targets
        rw [targets]; rfl
      obtain ⟨ρnext,copied,nextDefined,nextHeld⟩ := jump_successor_carry run scope dominated spec tag jump
        targetTag targetIndex target nextEvent nextBlock carriedAvailable cover post
        (by simpa only [spec.atBlock] using tDefined) crossed
      have nextReturned : Clif.runLoop env cp left ⟨fr',[],t.mem⟩ = .trapped code := by
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
      have finished := continuation left (by omega) ⟨fr',[],t.mem⟩ ρnext w' nextHeld.1.1 rfl bodyEq termEq
        nextDefined nextReturned nextHeld
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
      have whole := RunOkABIAt.prefix path finished
      simpa only [slotsEq] using whole

end Backend.Stock.Proof.Control

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `SuccessorReturnBelow` without the forward rank: the successor has a carry set `carried`,
and `cover` relates it to the predecessor's terminator state `term` and carry set `carry`. -/
structure SuccessorCarryReturnBelow (f : Clif.Function) (result : Result) (bc : Clif.BlockCall)
    (term : State) (carry : Nat → Prop) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (vals : List Clif.Val) (cm : Clif.Mem) (bound : Nat) where
  index : Nat
  targetLabel : Nat
  block : Clif.Block
  event : BlockScanEvent
  carried : Nat → Prop
  lookup : blockIdx? f bc.block = some index
  found : f.block? bc.block = some block
  tag : result.order.nodes[targetLabel]? = some (.original index)
  member : event ∈ result.blockScans.toList
  atBlock : event.block = index
  available : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) index 0
  cover : EdgeCover f result index (block.params.map (·.1)) event.output.state carried term carry
  returns : ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = block.body → s.frame.term = block.term →
    SourceDefinedAt f result.ctx index 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    Inherited.CarryRel f result event.ctx event.block MR carried event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨targetLabel,0,ρ,w⟩ (.returned vals cm)

/-- `SuccessorTrapBelow` without the forward rank, with carry sets as in
`SuccessorCarryReturnBelow`. -/
structure SuccessorCarryTrapBelow (f : Clif.Function) (result : Result) (bc : Clif.BlockCall)
    (term : State) (carry : Nat → Prop) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (trapCode : Clif.TrapCode) (bound : Nat) where
  index : Nat
  targetLabel : Nat
  block : Clif.Block
  event : BlockScanEvent
  carried : Nat → Prop
  lookup : blockIdx? f bc.block = some index
  found : f.block? bc.block = some block
  tag : result.order.nodes[targetLabel]? = some (.original index)
  member : event ∈ result.blockScans.toList
  atBlock : event.block = index
  available : ∀ x,carried x → x ∈ availOf f (availIn f result.ctx) index 0
  cover : EdgeCover f result index (block.params.map (·.1)) event.output.state carried term carry
  traps : ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = block.body → s.frame.term = block.term →
    SourceDefinedAt f result.ctx index 0 s.frame → Clif.runLoop env cp fuel s = .trapped trapCode →
    Inherited.CarryRel f result event.ctx event.block MR carried event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨targetLabel,0,ρ,w⟩ (.trapped trapCode)

/-- The demand order of a forward successor of an actual conditional block. -/
private theorem forward_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {targetLabel index : Nat} {event : BlockScanEvent} (member : event ∈ result.blockScans.toList)
    (atBlock : event.block = index) (targetTag : result.order.nodes[targetLabel]? = some (.original index))
    (forward : label < targetLabel) :
    ∀ (x : Nat),event.output.state.demand[x]! ≤ spec.term.output.state.demand[x]! := by
  have eventTag : result.order.nodes[targetLabel]? = some (.original event.block) := by
    rw [atBlock]; exact targetTag
  exact CfgDemand.ordered_scan_demand_of_labels run scope
    (Array.getElem?_eq_some_iff.mp eventTag).1 forward
    (by simp only [getElem!_def,eventTag,Option.getD_some])
    (by simp only [getElem!_def,tag,Option.getD_some,spec.atBlock]) member spec.events spec.split

/-- A forward successor family is a carry successor family whose successors carry nothing; the
forward rank supplies the edge cover. -/
theorem ConditionalBodySpec.successor_returns_carry_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {vals : List Clif.Val} {cm : Clif.Mem} {bound : Nat} (carry : Nat → Prop)
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorReturnBelow f result label bc isem MR env cp vals cm bound)) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm bound) :=
  fun index bc selected => by
    obtain ⟨next⟩ := successors index bc selected
    exact ⟨{
      index := next.index
      targetLabel := next.targetLabel
      block := next.block
      event := next.event
      carried := fun _ => False
      lookup := next.lookup
      found := next.found
      tag := next.tag
      member := next.member
      atBlock := next.atBlock
      available := fun _ kept => kept.elim
      cover := EdgeCover.of_demand (forward_demand run scope spec tag next.member next.atBlock next.tag next.forward)
        (fun _ kept => kept.elim)
      returns := fun fuel lt s ρ w func callers body term defined returned held =>
        next.returns fuel lt s ρ w func callers body term defined returned held.1 }⟩

/-- A forward trap successor family is a carry successor family whose successors carry nothing. -/
theorem ConditionalBodySpec.successor_traps_carry_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {trapCode : Clif.TrapCode} {bound : Nat} (carry : Nat → Prop)
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorTrapBelow f result label bc isem MR env cp trapCode bound)) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode bound) :=
  fun index bc selected => by
    obtain ⟨next⟩ := successors index bc selected
    exact ⟨{
      index := next.index
      targetLabel := next.targetLabel
      block := next.block
      event := next.event
      carried := fun _ => False
      lookup := next.lookup
      found := next.found
      tag := next.tag
      member := next.member
      atBlock := next.atBlock
      available := fun _ kept => kept.elim
      cover := EdgeCover.of_demand (forward_demand run scope spec tag next.member next.atBlock next.tag next.forward)
        (fun _ kept => kept.elim)
      traps := fun fuel lt s ρ w func callers body term defined trapped held =>
        next.traps fuel lt s ρ w func callers body term defined trapped held.1 }⟩

/-- `returning_empty_parameter_below` with carry sets: the block holds `CarryRel` of `carry` at
entry, and each selected successor continuation needs `CarryRel` of its own carry set. -/
theorem ConditionalBodySpec.returning_empty_parameter_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_parameter_carry_core run scope dominated family refines driver stable
      termShape parameter conditionTy available remaining atTerm defined returned held
  let bc := if Clif.Sem.truthy value.bits then yes else no
  let choice := if Clif.Sem.truthy value.bits then 0 else 1
  have selected : (dests b.term)[choice]? = some bc := by
    cases truth : Clif.Sem.truthy value.bits <;> simp [dests,termShape,choice,bc,truth]
  obtain ⟨next⟩ := successors choice bc selected
  have nextBlock : next.event.block = sourceTargetIndex f bc := by
    simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
  have arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx t.frame
      (fun key => regs (aliasNum result.final.alias key)) := by
    intro x member
    have noArgs : bc.args = [] := by
      dsimp only [bc]
      split <;> simp_all only [emptyArgs.1,emptyArgs.2]
    rw [noArgs] at member
    cases member
  have carriedAvailable : ∀ x,next.carried x →
      x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
    intro x kept
    rw [next.atBlock]
    exact next.available x kept
  have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
      next.carried spec.term.output.state carry := by
    rw [next.atBlock]
    simp only [sourceTargetParams,next.found,Option.getD_some]
    exact next.cover
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
      carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left (by omega) {t with frame := fr} ρnext endWorld
    nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
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
  have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
      (spec.raw.insts.map (·.mapRegs resolve)).size := by
    simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
    omega
  have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
  have whole := RunOkABIAt.prefix path finished
  simpa only [slotEq] using whole

/-- `trapping_empty_parameter_below` with carry sets. -/
theorem ConditionalBodySpec.trapping_empty_parameter_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    (emptyArgs : yes.args = [] ∧ no.args = [])
    {carry : Nat → Prop}
    (available : ∀ x,carry x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) := by
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
  have carried' := spec.trapping_parameter_carry_core run scope dominated family refines driver stable
    termShape parameter conditionTy available remaining atTerm defined returned held
  rcases carried' with failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩
  · obtain ⟨offset,i,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failed
    obtain ⟨path,bound,instruction,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    exact ⟨label,spec.preludeCode.size+offset,regs,prefixWorld,_,i,ops,outs,endWorld,path,
      spec.placed,instruction,operands,semantics,coded⟩
  · let bc := if Clif.Sem.truthy value.bits then yes else no
    let choice := if Clif.Sem.truthy value.bits then 0 else 1
    have selected : (dests b.term)[choice]? = some bc := by
      cases truth : Clif.Sem.truthy value.bits <;> simp [dests,termShape,choice,bc,truth]
    obtain ⟨next⟩ := successors choice bc selected
    have nextBlock : next.event.block = sourceTargetIndex f bc := by
      simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
    have arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx t.frame
        (fun key => regs (aliasNum result.final.alias key)) := by
      intro x member
      have noArgs : bc.args = [] := by
        dsimp only [bc]
        split <;> simp_all only [emptyArgs.1,emptyArgs.2]
      rw [noArgs] at member
      cases member
    have carriedAvailable : ∀ x,next.carried x →
        x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
      intro x kept
      rw [next.atBlock]
      exact next.available x kept
    have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
        next.carried spec.term.output.state carry := by
      rw [next.atBlock]
      simp only [sourceTargetParams,next.found,Option.getD_some]
      exact next.cover
    obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
      spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
        carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
    have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
    subst tl
    have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
      (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
    subst targetLabel
    obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = next.block := by
      rw [post.1.1] at found
      exact Option.some.inj (found.symm.trans next.found)
    have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
    have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
    have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := next.traps left (by omega) {t with frame := fr} ρnext endWorld
      nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
    have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
      omega
    have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotEq] using whole

end Backend.Stock.Proof.ConditionalValues

import FV.Backend.Proof.StockForwardTrap
import FV.Backend.Proof.StockConditionalReturnAt
import FV.Backend.Proof.StockConditionalTrapAt

/-! Fuel-bounded block compositions for CFGs with loops (#140, T7b-2).

The forward compositions require the successor continuation for every fuel, which only an
induction on the block rank supplies. A loop composition by strong induction on the source fuel
supplies it only below the current fuel. Every block below executes its body and its terminator
before it enters the successor (`left+1+b.body.length = fuel` in the per-block cores), so these
bounded copies require the successor continuation only for that strictly smaller fuel. The
`forward` and demand premises are unchanged. -/

namespace Backend.Stock.Proof.ForwardSource
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false

/-- `ReturnsAt` for source runs with fuel below `bound`. -/
def ReturnsBelow (f : Clif.Function) (result : Result) (label bi : Nat) (b : Clif.Block)
    (event : BlockScanEvent) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) : Prop :=
  ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem)
    (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.returned vals cm)

/-- `TrapsAt` for source runs with fuel below `bound`. -/
def TrapsBelow (f : Clif.Function) (result : Result) (label bi : Nat) (b : Clif.Block)
    (event : BlockScanEvent) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) : Prop :=
  ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (code : Clif.TrapCode)
    (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.trapped code)

/-- An all-fuel return continuation holds below every bound. -/
theorem ReturnsAt.below {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (returns : ReturnsAt f result label bi b event isem MR env cp) (bound : Nat) :
    ReturnsBelow f result label bi b event isem MR env cp bound :=
  fun fuel _ => returns fuel

/-- A return continuation below every bound holds for all fuel. -/
theorem returnsAt_of_below {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (returns : ∀ bound,ReturnsBelow f result label bi b event isem MR env cp bound) :
    ReturnsAt f result label bi b event isem MR env cp :=
  fun fuel => returns (fuel+1) fuel (Nat.lt_succ_self fuel)

/-- A bounded continuation holds below every smaller bound. -/
theorem ReturnsBelow.mono {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {bound bound' : Nat} (le : bound ≤ bound')
    (returns : ReturnsBelow f result label bi b event isem MR env cp bound') :
    ReturnsBelow f result label bi b event isem MR env cp bound :=
  fun fuel lt => returns fuel (Nat.lt_of_lt_of_le lt le)

/-- An all-fuel trap continuation holds below every bound. -/
theorem TrapsAt.below {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (traps : TrapsAt f result label bi b event isem MR env cp) (bound : Nat) :
    TrapsBelow f result label bi b event isem MR env cp bound :=
  fun fuel _ => traps fuel

/-- A trap continuation below every bound holds for all fuel. -/
theorem trapsAt_of_below {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (traps : ∀ bound,TrapsBelow f result label bi b event isem MR env cp bound) :
    TrapsAt f result label bi b event isem MR env cp :=
  fun fuel => traps (fuel+1) fuel (Nat.lt_succ_self fuel)

/-- A bounded continuation holds below every smaller bound. -/
theorem TrapsBelow.mono {f : Clif.Function} {result : Result} {label bi : Nat} {b : Clif.Block}
    {event : BlockScanEvent} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {bound bound' : Nat} (le : bound ≤ bound')
    (traps : TrapsBelow f result label bi b event isem MR env cp bound') :
    TrapsBelow f result label bi b event isem MR env cp bound :=
  fun fuel lt => traps fuel (Nat.lt_of_lt_of_le lt le)

end Backend.Stock.Proof.ForwardSource

namespace Backend.Stock.Proof.Control
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `jump_body_returns_at` with the successor continuation required only below the fuel of
the jump block's own source run. -/
theorem jump_body_returns_below {f : Clif.Function} {result : Result}
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
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {vals : List Clif.Val} {outMem : Clif.Mem} {fuel : Nat}
    (continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp left s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.returned vals outMem))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨t,left,ρ',w',total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩ :=
    Inherited.scalar_jump_carry_returns_defined run scope dominated refines driver stable spec jump formats
      (family b (List.mem_of_getElem? source)) (needed := fun _ => False)
      (by intro x h; cases h) remaining atTerm returned
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
    have finished := continuation left (by omega) ⟨fr',[],t.mem⟩ ρnext w' nextHeld.1 rfl bodyEq termEq
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

/-- `jump_body_traps_at` with the successor continuation required only below the fuel of
the jump block's own source run. -/
theorem jump_body_traps_below {f : Clif.Function} {result : Result}
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
    (demand : ∀ (x : Nat),next.output.state.demand[x]! ≤ spec.term.output.state.demand[x]!)
    {code : Clif.TrapCode} {fuel : Nat}
    (continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp left s = .trapped code →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.trapped code))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w) :
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
  have carry :=
    Inherited.scalar_jump_carry_traps_or_continues_defined run scope dominated refines driver stable spec jump formats
      (family b (List.mem_of_getElem? source)) (needed := fun _ => False)
      (by intro x h; cases h) remaining atTerm returned
      ⟨held,by intro x h; cases h⟩ defined
  rcases carry with failed | continuedBody
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
      obtain ⟨ρnext,copied,nextDefined,nextHeld⟩ := direct_successor_guarded_of_demand run scope dominated
        spec.events nextEvent tag source (by simp [jump,dests]) successor targetTag targetIndex target
        spec.atBlock nextBlock post.1 (by simpa only [spec.atBlock] using tDefined) crossed
        (jump_successor_values_of_demand run scope dominated spec jump targetTag targetIndex target nextBlock demand post.1)
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
      have finished := continuation left (by omega) ⟨fr',[],t.mem⟩ ρnext w' nextHeld.1 rfl bodyEq termEq
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
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `SuccessorReturn` whose continuation is required only for fuel below `bound`. -/
structure SuccessorReturnBelow (f : Clif.Function) (result : Result) (label : Nat)
    (bc : Clif.BlockCall) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (vals : List Clif.Val) (cm : Clif.Mem) (bound : Nat) where
  index : Nat
  targetLabel : Nat
  block : Clif.Block
  event : BlockScanEvent
  lookup : blockIdx? f bc.block = some index
  found : f.block? bc.block = some block
  tag : result.order.nodes[targetLabel]? = some (.original index)
  member : event ∈ result.blockScans.toList
  atBlock : event.block = index
  forward : label < targetLabel
  returns : ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = block.body → s.frame.term = block.term →
    SourceDefinedAt f result.ctx index 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨targetLabel,0,ρ,w⟩ (.returned vals cm)

/-- `SuccessorTrap` whose continuation is required only for fuel below `bound`. -/
structure SuccessorTrapBelow (f : Clif.Function) (result : Result) (label : Nat)
    (bc : Clif.BlockCall) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (trapCode : Clif.TrapCode) (bound : Nat) where
  index : Nat
  targetLabel : Nat
  block : Clif.Block
  event : BlockScanEvent
  lookup : blockIdx? f bc.block = some index
  found : f.block? bc.block = some block
  tag : result.order.nodes[targetLabel]? = some (.original index)
  member : event ∈ result.blockScans.toList
  atBlock : event.block = index
  forward : label < targetLabel
  traps : ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = block.body → s.frame.term = block.term →
    SourceDefinedAt f result.ctx index 0 s.frame → Clif.runLoop env cp fuel s = .trapped trapCode →
    GuardedScanRel f result event.ctx event.block MR event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨targetLabel,0,ρ,w⟩ (.trapped trapCode)

/-- An all-fuel successor return continuation, restricted below `bound`. -/
def SuccessorReturn.below {f : Clif.Function} {result : Result} {label : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {vals : List Clif.Val} {cm : Clif.Mem}
    (next : SuccessorReturn f result label bc isem MR env cp vals cm) (bound : Nat) :
    SuccessorReturnBelow f result label bc isem MR env cp vals cm bound :=
  { index := next.index, targetLabel := next.targetLabel, block := next.block, event := next.event,
    lookup := next.lookup, found := next.found, tag := next.tag, member := next.member,
    atBlock := next.atBlock, forward := next.forward, returns := fun fuel _ => next.returns fuel }

/-- An all-fuel successor trap continuation, restricted below `bound`. -/
def SuccessorTrap.below {f : Clif.Function} {result : Result} {label : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {trapCode : Clif.TrapCode}
    (next : SuccessorTrap f result label bc isem MR env cp trapCode) (bound : Nat) :
    SuccessorTrapBelow f result label bc isem MR env cp trapCode bound :=
  { index := next.index, targetLabel := next.targetLabel, block := next.block, event := next.event,
    lookup := next.lookup, found := next.found, tag := next.tag, member := next.member,
    atBlock := next.atBlock, forward := next.forward, traps := fun fuel _ => next.traps fuel }

/-- The successor family of the forward return composition gives the bounded family. -/
theorem successor_returns_below {f : Clif.Function} {result : Result} {label : Nat} {b : Clif.Block}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {vals : List Clif.Val} {cm : Clif.Mem}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm)) (bound : Nat) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorReturnBelow f result label bc isem MR env cp vals cm bound) :=
  fun index bc selected => by
    obtain ⟨next⟩ := successors index bc selected
    exact ⟨next.below bound⟩

/-- The successor family of the forward trap composition gives the bounded family. -/
theorem successor_traps_below {f : Clif.Function} {result : Result} {label : Nat} {b : Clif.Block}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {trapCode : Clif.TrapCode}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorTrap f result label bc isem MR env cp trapCode)) (bound : Nat) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorTrapBelow f result label bc isem MR env cp trapCode bound) :=
  fun index bc selected => by
    obtain ⟨next⟩ := successors index bc selected
    exact ⟨next.below bound⟩

/-- `ConditionalBodySpec.returning_empty_parameter_at` with each selected successor
continuation required only below the fuel of the conditional block's own source run. -/
theorem ConditionalBodySpec.returning_empty_parameter_below
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
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorReturnBelow f result label bc isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_parameter_core run scope dominated family refines driver stable
      termShape parameter conditionTy remaining atTerm defined returned held
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
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_guarded run scope dominated tag selected next.member nextBlock
      (by simpa only [next.atBlock] using next.tag) next.forward post
      (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left (by omega) {t with frame := fr} ρnext endWorld
    nextHeld.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
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

/-- `ConditionalBodySpec.trapping_empty_parameter_at` with each selected successor
continuation required only below the fuel of the conditional block's own source run. -/
theorem ConditionalBodySpec.trapping_empty_parameter_below
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
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorTrapBelow f result label bc isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ world) :
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
  have carry := spec.trapping_parameter_core run scope dominated family refines driver stable
    termShape parameter conditionTy remaining atTerm defined returned held
  rcases carry with failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩
  · obtain ⟨offset,i,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failed
    obtain ⟨path,bound,instruction,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    exact ⟨label,spec.preludeCode.size+offset,regs,prefixWorld,_,i,ops,outs,endWorld,path,
      spec.placed,instruction,operands,semantics,coded⟩
  ·
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
    obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
      spec.selected_successor_guarded run scope dominated tag selected next.member nextBlock
        (by simpa only [next.atBlock] using next.tag) next.forward post
        (by simpa only [spec.atBlock] using tDefined) crossed arguments
    have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
    subst tl
    have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
      (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
    subst targetLabel
    obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = next.block := by
      rw [post.1] at found
      exact Option.some.inj (found.symm.trans next.found)
    have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
    have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
    have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := next.traps left (by omega) {t with frame := fr} ρnext endWorld
      nextHeld.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
    have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
      omega
    have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotEq] using whole

end Backend.Stock.Proof.ConditionalValues

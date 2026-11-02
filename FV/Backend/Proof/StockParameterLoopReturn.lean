import FV.Backend.Proof.StockLoopDefBefore
import FV.Backend.Proof.StockParameterLeaf
import FV.Backend.Proof.StockCfgTraversalScans

/-! Return composition of the loop parameter class (#140, T7b-5).

The forward compositions (`nonentry_parameter_returns_of_leaf`) go by induction on the block
rank, so each successor continuation holds for all fuel. With back edges no rank exists. Here
the induction goes on the source fuel, over all nonentry original blocks at once
(`loop_returns_below`): each block executes its body and its terminator before it enters a
successor, so the successor continuation is needed only for smaller fuel
(`jump_body_carry_returns_below`, `returning_empty_parameter_carry_below`).

Each block holds `CarryRel` of its definition carry `defCarry` at entry, and every source edge,
forward or back, is covered by the definition carries (`stock_defCarry_cover`). The entry block
carries nothing, so `GuardedScanRel` at the entry starts the composition (`StockParameterLoopDomain`). -/

namespace Backend.Stock.Proof.ParameterLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `ReturnsBelow` with `CarryRel` of the block's definition carry at entry in place of
`GuardedScanRel`. -/
def CarryReturnsBelow (f : Clif.Function) (result : Result) (label bi : Nat) (b : Clif.Block)
    (event : BlockScanEvent) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) : Prop :=
  ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem)
    (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
    Inherited.CarryRel f result event.ctx event.block MR (defCarry f result bi)
      event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.returned vals cm)

/-- Every original node has the scan event of its block. -/
theorem original_event {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result)
    {label bi : Nat} (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi := by
  obtain ⟨ranges,params,input,data,core,raw,preludeCode,coreRun,assembled,build,sizes,prepared,
    events,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  exact ⟨core.scan,events,atBlock⟩

/-- `selected_ranked_target` without the rank: a selected successor is an original nonentry
block with an original node. -/
theorem selected_loop_target {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    (selected : (dests b.term)[index]? = some bc) :
    ∃ (tl targetLabel : Nat) (target : Clif.Block),blockIdx? f bc.block = some tl ∧
      f.block? bc.block = some target ∧
      f.blocks[tl]? = some target ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      tl ≠ 0 := by
  obtain ⟨tl,middle,lookup,nonentry,successor,node⟩ := stock_lower_selected_successor run scope tag block selected
  have target : ∃ (targetLabel : Nat),result.order.nodes[targetLabel]? = some (.original tl) := by
    rcases node with original | synthetic
    · exact ⟨middle,original⟩
    · obtain ⟨input,next,args,targetLabel,call,successors,targetTag,placed⟩ := stock_lower_critical_code run synthetic
      exact ⟨targetLabel,targetTag⟩
  obtain ⟨targetLabel,targetTag⟩ := target
  obtain ⟨targetBlock,found,sourceBlock⟩ := block?_of_idx lookup
  exact ⟨tl,targetLabel,targetBlock,lookup,found,sourceBlock,targetTag,nonentry⟩

/-- A selected successor is a source successor. -/
theorem selected_succIdx {f : Clif.Function} {bi index tl : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (block : f.blocks[bi]? = some b) (selected : (dests b.term)[index]? = some bc)
    (lookup : blockIdx? f bc.block = some tl) : tl ∈ succIdx f bi := by
  have member : bc ∈ dests b.term := List.mem_of_getElem? selected
  have edge : bc.block ∈ succIds b.term := by
    cases term : b.term <;> rw [term] at member <;> simp only [dests,List.not_mem_nil] at member <;>
      simp only [succIds,dests] <;> exact List.mem_map.mpr ⟨bc,member,rfl⟩
  simp only [succIdx,block]
  exact List.mem_filterMap.mpr ⟨bc.block,edge,lookup⟩

/-- A jump's target is a source successor. -/
theorem jump_succIdx {f : Clif.Function} {bi tl : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (block : f.blocks[bi]? = some b) (jump : b.term = .jump bc)
    (lookup : blockIdx? f bc.block = some tl) : tl ∈ succIdx f bi :=
  selected_succIdx block (index := 0) (by simp [dests,jump]) lookup

theorem local_family {f : Clif.Function} {b : Clif.Block} {bi : Nat}
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) (source : f.blocks[bi]? = some b) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family b (List.mem_of_getElem? source) stm member with
    (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- A jump block of the loop class, entry or not: it holds its definition carry at entry, and
its target continues below the block's fuel with the target's definition carry. -/
theorem jump_carry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi)) (jump : b.term = .jump bc)
    {fuel : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryReturnsBelow f result targetLabel tl targetBlock next isem MR env cp fuel)
    {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx bi 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (defCarry f result bi)
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals cm) := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
    CriticalOwners.jump_successor run scope tag block jump
  have sameTarget : spec.target = targetLabel := by
    have row : result.order.successors[label]! = #[targetLabel] := by
      simp only [getElem!_def,successors]
    have targets := spec.targets
    rw [row] at targets
    exact (List.cons.inj targets).1.symm
  obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
  obtain ⟨next,nextEvent,nextBlock⟩ := original_event run targetTag
  have cover := stock_defCarry_cover run scope dominated.ssa spec.events spec.split
    (by rw [spec.atBlock]; exact tag) nextEvent (by rw [nextBlock]; exact targetTag)
    (by rw [nextBlock]; exact targetSource) (by rw [nextBlock,spec.atBlock]; exact jump_succIdx block jump targetIndex)
  rw [nextBlock,spec.atBlock] at cover
  have continuation : ∀ (left : Nat),left < fuel → ∀ (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp left s = .returned vals cm →
      Inherited.CarryRel f result next.ctx next.block MR (defCarry f result tl) next.output.state
        (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.returned vals cm) := by
    intro left lower t ρ' w' func' callers' remaining' atTerm' defined' returned' held'
    rw [sameTarget]
    exact continued targetTag targetSource targetNonentry nextEvent nextBlock left lower t vals cm ρ' w'
      func' callers' remaining' atTerm' defined' returned' held'
  exact Control.jump_body_carry_returns_below run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock
    (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept) defCarry_available cover
    continuation callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held

/-- The successor family of a parameter branch of the loop class, entry or not: each selected
successor carries its definition carry, which the edge cover relates to the branch block's. -/
theorem conditional_carry_successors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {vals : List Clif.Val} {cm : Clif.Mem} {bound : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryReturnsBelow f result targetLabel tl targetBlock next isem MR env cp bound) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state (defCarry f result bi)
        isem MR env cp vals cm bound) := by
  intro index bc selected
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry⟩ :=
    selected_loop_target run scope tag block selected
  obtain ⟨next,nextEvent,nextBlock⟩ := original_event run targetTag
  have cover := stock_defCarry_cover run scope dominated.ssa spec.events spec.split
    (by rw [spec.atBlock]; exact tag) nextEvent (by rw [nextBlock]; exact targetTag)
    (by rw [nextBlock]; exact source) (by rw [nextBlock,spec.atBlock]; exact selected_succIdx block selected lookup)
  rw [nextBlock,spec.atBlock] at cover
  exact ⟨{
    index := tl
    targetLabel := targetLabel
    block := targetBlock
    event := next
    carried := defCarry f result tl
    lookup := lookup
    found := found
    tag := targetTag
    member := nextEvent
    atBlock := nextBlock
    available := defCarry_available
    cover := cover
    returns := fun left lower t ρ' w' =>
      continued targetTag source targetNonentry nextEvent nextBlock left lower t vals cm ρ' w' }⟩

/-- A parameter branch of the loop class, entry or not. -/
theorem conditional_carry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (parameter : ParameterCondition f c)
    {fuel : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryReturnsBelow f result targetLabel tl targetBlock next isem MR env cp fuel)
    {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx bi 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (defCarry f result bi)
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals cm) := by
  have metadata := parameter_metadata parameter dominated.ssa spec.build
  exact spec.returning_empty_parameter_carry_below run scope dominated family refines driver stable
    tag term metadata.1 metadata.2 ⟨yesEmpty,noEmpty⟩
    (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
    (conditional_carry_successors run scope dominated spec tag continued)
    callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held

/-- **Loop returns below every fuel bound.** By strong induction on the bound, every nonentry
original block of the loop class returns as its machine code from `CarryRel` of its definition
carry. No rank or forward premise is used: targets may be loop headers. -/
theorem loop_returns_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) :
    ∀ {label bi : Nat} {b : Clif.Block} {event : BlockScanEvent},
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      event ∈ result.blockScans.toList → event.block = bi →
      CarryReturnsBelow f result label bi b event isem MR env cp bound := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro label bi b event tag block nonentry member atBlock
    intro fuel lt s vals cm ρ w func callers remaining atTerm defined returned held
    have continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
        result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
        next ∈ result.blockScans.toList → next.block = tl →
        CarryReturnsBelow f result targetLabel tl targetBlock next isem MR env cp fuel :=
      fun targetTag targetSource targetNonentry nextEvent nextBlock =>
        ih fuel lt targetTag targetSource targetNonentry nextEvent nextBlock
    rcases terms bi b block nonentry with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
    · obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag block jump
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := jump_carry_returns run scope dominated family refines driver stable spec tag jump
        continued callers remaining atTerm defined returned held
      simpa only [jump_nonentry_prelude spec nonentry] using finished
    · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := CfgReturnAt.return_block_returns_at run scope dominated abi family ret refines driver
        stable spec func callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held.1
      simpa only [spec.noPrelude nonentry] using finished
    · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := conditional_carry_returns run scope dominated family refines driver stable spec tag
        term yesEmpty noEmpty parameter continued callers remaining atTerm defined returned held
      simpa only [conditional_nonentry_prelude spec nonentry] using finished
    · exact absurd returned (TrapBody.trap_source_noreturn (local_family family block) (j := 0)
        (by simpa using remaining) (atTerm.trans trap))

/-- `loop_returns_below` for all fuel. -/
theorem loop_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block} {event : BlockScanEvent}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    (nonentry : bi ≠ 0) (member : event ∈ result.blockScans.toList) (atBlock : event.block = bi) :
    ∀ (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
      SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
      Inherited.CarryRel f result event.ctx event.block MR (defCarry f result bi)
        event.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.returned vals cm) :=
  fun fuel => loop_returns_below run scope dominated abi terms family refines driver stable env cp (fuel+1)
    tag block nonentry member atBlock fuel (Nat.lt_succ_self fuel)

end Backend.Stock.Proof.ParameterLoopCfg

import FV.Backend.Proof.StockParameterLoopReturn

/-! First-trap composition of the loop parameter class (#140, T7b-5): `StockParameterLoopReturn`
for traps. The induction goes on the source fuel over all nonentry original blocks; a `trap`
leaf traps in its body or at its terminator, and a return leaf traps in its body. -/

namespace Backend.Stock.Proof.ParameterLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- `TrapsBelow` with `CarryRel` of the block's definition carry at entry in place of
`GuardedScanRel`. -/
def CarryTrapsBelow (f : Clif.Function) (result : Result) (label bi : Nat) (b : Clif.Block)
    (event : BlockScanEvent) (isem : Backend.Proof.Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) : Prop :=
  ∀ (fuel : Nat),fuel < bound → ∀ (s : Clif.State) (code : Clif.TrapCode)
    (ρ : Nat → CV) (w : Arm.ArmState),
    s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
    SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
    Inherited.CarryRel f result event.ctx event.block MR (defCarry f result bi)
      event.output.state (0,s.frame,s.mem) ρ w →
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.trapped code)

/-- A jump block of the loop class, entry or not, for first traps. -/
theorem jump_carry_traps {f : Clif.Function} {result : Result}
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
      CarryTrapsBelow f result targetLabel tl targetBlock next isem MR env cp fuel)
    {s : Clif.State} {code : Clif.TrapCode} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx bi 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (defCarry f result bi)
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.trapped code) := by
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
      Clif.runLoop env cp left s = .trapped code →
      Inherited.CarryRel f result next.ctx next.block MR (defCarry f result tl) next.output.state
        (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
    intro left lower t ρ' w' func' callers' remaining' atTerm' defined' trapped' held'
    rw [sameTarget]
    exact continued targetTag targetSource targetNonentry nextEvent nextBlock left lower t code ρ' w'
      func' callers' remaining' atTerm' defined' trapped' held'
  exact Control.jump_body_carry_traps_below run scope dominated family refines driver stable spec tag jump
    (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock
    (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept) defCarry_available cover
    continuation callers remaining atTerm (by simpa only [spec.atBlock] using defined) trapped held

/-- The first-trap successor family of a parameter branch of the loop class, entry or not. -/
theorem conditional_carry_trap_successors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {code : Clif.TrapCode} {bound : Nat}
    (continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
      result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
      next ∈ result.blockScans.toList → next.block = tl →
      CarryTrapsBelow f result targetLabel tl targetBlock next isem MR env cp bound) :
    ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state (defCarry f result bi)
        isem MR env cp code bound) := by
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
    traps := fun left lower t ρ' w' =>
      continued targetTag source targetNonentry nextEvent nextBlock left lower t code ρ' w' }⟩

/-- A parameter branch of the loop class, entry or not, for first traps. -/
theorem conditional_carry_traps {f : Clif.Function} {result : Result}
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
      CarryTrapsBelow f result targetLabel tl targetBlock next isem MR env cp fuel)
    {s : Clif.State} {code : Clif.TrapCode} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx bi 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR (defCarry f result bi)
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.trapped code) := by
  have metadata := parameter_metadata parameter dominated.ssa spec.build
  exact spec.trapping_empty_parameter_carry_below run scope dominated family refines driver stable
    tag term metadata.1 metadata.2 ⟨yesEmpty,noEmpty⟩
    (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
    (conditional_carry_trap_successors run scope dominated spec tag continued)
    callers remaining atTerm (by simpa only [spec.atBlock] using defined) trapped held

/-- **Loop first traps below every fuel bound**, by strong induction on the bound over every
nonentry original block of the loop class. -/
theorem loop_traps_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) (bound : Nat) :
    ∀ {label bi : Nat} {b : Clif.Block} {event : BlockScanEvent},
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      event ∈ result.blockScans.toList → event.block = bi →
      CarryTrapsBelow f result label bi b event isem MR env cp bound := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro label bi b event tag block nonentry member atBlock
    intro fuel lt s code ρ w func callers remaining atTerm defined trapped held
    have continued : ∀ {targetLabel tl : Nat} {targetBlock : Clif.Block} {next : BlockScanEvent},
        result.order.nodes[targetLabel]? = some (.original tl) → f.blocks[tl]? = some targetBlock → tl ≠ 0 →
        next ∈ result.blockScans.toList → next.block = tl →
        CarryTrapsBelow f result targetLabel tl targetBlock next isem MR env cp fuel :=
      fun targetTag targetSource targetNonentry nextEvent nextBlock =>
        ih fuel lt targetTag targetSource targetNonentry nextEvent nextBlock
    rcases terms bi b block nonentry with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
    · obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag block jump
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := jump_carry_traps run scope dominated family refines driver stable spec tag jump
        continued callers remaining atTerm defined trapped held
      simpa only [jump_nonentry_prelude spec nonentry] using finished
    · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret refines driver
        stable spec callers remaining atTerm trapped held.1
      simpa only [spec.noPrelude nonentry] using finished
    · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term
        refines driver stable env cp
      have same : spec.core.scan = event :=
        CfgTrace.actual_scan_unique run scope spec.events member (spec.atBlock.trans atBlock.symm)
      subst same
      have finished := conditional_carry_traps run scope dominated family refines driver stable spec tag
        term yesEmpty noEmpty parameter continued callers remaining atTerm defined trapped held
      simpa only [conditional_nonentry_prelude spec nonentry] using finished
    · obtain ⟨leaf,raw,preludeCode,events,leafBlock,rawCode,noPrelude,placed⟩ :=
        ConditionalValues.stock_lower_trap_block_code run tag block trap
      have same : leaf = event := CfgTrace.actual_scan_unique run scope events member (leafBlock.trans atBlock.symm)
      subst same
      have finished := ConditionalValues.trap_block_traps_at run scope dominated family block trap
        refines driver stable events leafBlock rawCode placed remaining atTerm trapped held.1
      simpa only [noPrelude nonentry] using finished

/-- `loop_traps_below` for all fuel. -/
theorem loop_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block} {event : BlockScanEvent}
    (tag : result.order.nodes[label]? = some (.original bi)) (block : f.blocks[bi]? = some b)
    (nonentry : bi ≠ 0) (member : event ∈ result.blockScans.toList) (atBlock : event.block = bi) :
    ∀ (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = b.body → s.frame.term = b.term →
      SourceDefinedAt f result.ctx bi 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
      Inherited.CarryRel f result event.ctx event.block MR (defCarry f result bi)
        event.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨label,0,ρ,w⟩ (.trapped code) :=
  fun fuel => loop_traps_below run scope dominated abi terms family refines driver stable env cp (fuel+1)
    tag block nonentry member atBlock fuel (Nat.lt_succ_self fuel)

end Backend.Stock.Proof.ParameterLoopCfg

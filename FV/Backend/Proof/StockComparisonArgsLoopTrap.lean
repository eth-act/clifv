import FV.Backend.Proof.StockParameterArgsLoopTrap
import FV.Backend.Proof.StockComparisonArgsLoopReturn

/-! First-trap composition of the loop class with comparison branches and block arguments (#140,
T7b-9): `StockComparisonArgsLoopReturn` for traps. A branch dispatches on its condition metadata:
a parameter branch composes by `trapping_selected_parameter_carry_below`, a comparison branch by
`trapping_selected_comparison_carry_below`. Jump blocks and branch successor families are those of
the loop parameter class (`jump_carry_traps`, `conditional_carry_trap_successors`). -/

namespace Backend.Stock.Proof.ComparisonArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg Backend.Stock.Proof.ComparisonLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A branch of the class on a parameter or a comparison, with any block arguments, entry or
not, for first traps. -/
theorem branch_args_carry_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
  rcases condition_metadata condition dominated spec.build with metadata | comparison
  · exact spec.trapping_selected_parameter_carry_below run scope dominated family refines driver stable
      tag term metadata.1 metadata.2
      (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
      (conditional_carry_trap_successors run scope dominated spec tag continued)
      callers remaining atTerm (by simpa only [spec.atBlock] using defined) trapped held
  · exact spec.trapping_selected_comparison_carry_below run scope dominated family refines driver stable
      tag term comparison
      (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
      (conditional_carry_trap_successors run scope dominated spec tag continued)
      callers remaining atTerm (by simpa only [spec.atBlock] using defined) trapped held

/-- **Loop first traps below every fuel bound, with block arguments on parameter and comparison
branches**, by strong induction on the bound over every nonentry original block. -/
theorem comparison_args_loop_traps_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
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
    rcases terms bi b block with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,condition⟩ | ⟨leafCode,trap⟩
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
      have finished := branch_args_carry_traps run scope dominated family refines driver stable spec
        tag term condition continued callers remaining atTerm defined trapped held
      simpa only [conditional_nonentry_prelude spec nonentry] using finished
    · obtain ⟨leaf,raw,preludeCode,events,leafBlock,rawCode,noPrelude,placed⟩ :=
        ConditionalValues.stock_lower_trap_block_code run tag block trap
      have same : leaf = event := CfgTrace.actual_scan_unique run scope events member (leafBlock.trans atBlock.symm)
      subst same
      have finished := ConditionalValues.trap_block_traps_at run scope dominated family block trap
        refines driver stable events leafBlock rawCode placed remaining atTerm trapped held.1
      simpa only [noPrelude nonentry] using finished

/-- `comparison_args_loop_traps_below` for all fuel. -/
theorem comparison_args_loop_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ArgsLoopTerms f)
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
  fun fuel => comparison_args_loop_traps_below run scope dominated abi terms family refines driver stable
    env cp (fuel+1) tag block nonentry member atBlock fuel (Nat.lt_succ_self fuel)

end Backend.Stock.Proof.ComparisonArgsLoopCfg

import FV.Backend.Proof.StockParameterArgsLoopReturn
import FV.Backend.Proof.StockComparisonComputedArgsLoopClass

/-! Return composition of the loop class with computed comparisons and block arguments (#140,
CB-9).

`StockComparisonArgsLoopReturn` (T7b-9) with `ComputedArgsCondition`. The induction goes on the
source fuel over all nonentry original blocks (`computed_args_loop_returns_below`). Jump blocks
and the successor family of a branch are those of the loop parameter class (`jump_carry_returns`,
`conditional_carry_successors`). A branch dispatches on its condition metadata
(`condition_metadata`): a parameter branch composes by `returning_selected_parameter_carry_below`,
a comparison branch by `returning_selected_computed_zero_carry_below`, for a comparison in any form
of `ComputedZeroMetadata`. In both, the selected successor may take block arguments at an original
or a critical-edge successor. -/

namespace Backend.Stock.Proof.ComparisonComputedArgsLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg Backend.Stock.Proof.ComparisonLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A branch of the class on a parameter or a comparison, with any block arguments, entry or
not. -/
theorem branch_args_carry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (condition : ParameterCondition f c ∨ ComputedArgsCondition f c)
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
  rcases condition_metadata condition scope dominated spec.build with metadata | comparison
  · exact spec.returning_selected_parameter_carry_below run scope dominated family refines driver stable
      tag term metadata.1 metadata.2
      (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
      (conditional_carry_successors run scope dominated spec tag continued)
      callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
  · exact spec.returning_selected_computed_zero_carry_below run scope dominated family refines driver stable
      tag term comparison
      (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
      (conditional_carry_successors run scope dominated spec tag continued)
      callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held

/-- **Loop returns below every fuel bound, with block arguments on parameter and computed
comparison branches.** By strong induction on the bound, every nonentry original block returns as
its machine code from `CarryRel` of its definition carry. No rank or forward premise is used. -/
theorem computed_args_loop_returns_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
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
    rcases terms bi b block with
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,condition⟩ | ⟨leafCode,trap⟩
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
      have finished := branch_args_carry_returns run scope dominated family refines driver stable spec
        tag term condition continued callers remaining atTerm defined returned held
      simpa only [conditional_nonentry_prelude spec nonentry] using finished
    · exact absurd returned (TrapBody.trap_source_noreturn (local_family family block) (j := 0)
        (by simpa using remaining) (atTerm.trans trap))

/-- `computed_args_loop_returns_below` for all fuel. -/
theorem computed_args_loop_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : ComputedArgsTerms f)
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
  fun fuel => computed_args_loop_returns_below run scope dominated abi terms family refines driver stable
    env cp (fuel+1) tag block nonentry member atBlock fuel (Nat.lt_succ_self fuel)

end Backend.Stock.Proof.ComparisonComputedArgsLoopCfg

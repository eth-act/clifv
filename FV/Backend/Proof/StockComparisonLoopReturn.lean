import FV.Backend.Proof.StockParameterLoopReturn
import FV.Backend.Proof.StockComparisonLoopCarryBounded
import FV.Backend.Proof.StockComparisonLoopClass

/-! Return composition of the comparison loop class (#140, T7b-7).

`StockParameterLoopReturn` with a second kind of conditional block step: a branch on a
comparison (`comparison_carry_returns`, by `returning_empty_comparison_carry_below`). The
successor family and the definition carries are the same as for a parameter branch
(`conditional_carry_successors`, `stock_defCarry_cover`), so the induction on the source fuel
(`comparison_loop_returns_below`) dispatches the conditional step on the condition kind. -/

namespace Backend.Stock.Proof.ComparisonLoopCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ParameterCfg
  Backend.Stock.Proof.ParameterLoopCfg
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A comparison branch of the loop class, entry or not. -/
theorem comparison_carry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (comparison : ComparisonCondition f c)
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
  have metadata := comparison.metadata dominated spec.build
  exact spec.returning_empty_comparison_carry_below run scope dominated family refines driver stable
    tag term metadata ⟨yesEmpty,noEmpty⟩
    (fun x kept => by rw [spec.atBlock]; exact defCarry_available x kept)
    (conditional_carry_successors run scope dominated spec tag continued)
    callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held

/-- A branch of the loop class on a parameter or a comparison, entry or not. -/
theorem branch_carry_returns {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (condition : ParameterCondition f c ∨ ComparisonCondition f c)
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
  rcases condition with parameter | comparison
  · exact conditional_carry_returns run scope dominated family refines driver stable spec tag term
      yesEmpty noEmpty parameter continued callers remaining atTerm defined returned held
  · exact comparison_carry_returns run scope dominated family refines driver stable spec tag term
      yesEmpty noEmpty comparison continued callers remaining atTerm defined returned held

/-- **Comparison-loop returns below every fuel bound.** `loop_returns_below` of the parameter
loop class, with `LoopTerms`: by strong induction on the bound, every nonentry original block
returns as its machine code from `CarryRel` of its definition carry. -/
theorem comparison_loop_returns_below {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (terms : LoopTerms f)
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
      ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,condition⟩ | ⟨leafCode,trap⟩
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
      have finished := branch_carry_returns run scope dominated family refines driver stable spec tag
        term yesEmpty noEmpty condition continued callers remaining atTerm defined returned held
      simpa only [conditional_nonentry_prelude spec nonentry] using finished
    · exact absurd returned (TrapBody.trap_source_noreturn (local_family family block) (j := 0)
        (by simpa using remaining) (atTerm.trans trap))

end Backend.Stock.Proof.ComparisonLoopCfg

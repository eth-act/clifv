import FV.Backend.Proof.StockParameterTerms
import FV.Backend.Proof.StockConditionalTrapAt
import FV.Backend.Proof.StockForwardTrap
import FV.Backend.Proof.StockParameterSelection
import FV.Backend.Proof.StockParameterPrelude

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem nonentry_parameter_traps {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (nonentry : bi ≠ 0) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
      TrapsAt f result label bi b event isem MR env cp := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  obtain ⟨source,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have composed : ∀ n label bi b,result.order.nodes.size-label = n →
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
        TrapsAt f result label bi b event isem MR env cp := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro label bi b count tag block nonentry
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩
      · obtain ⟨spec⟩ := Control.stock_lower_jump_body_spec run scope dominated family tag block jump refines driver stable env cp
        obtain ⟨tl,targetLabel,targetIndex,targetNonentry,successors,targetTag⟩ :=
          CriticalOwners.jump_successor run scope tag block jump
        have sameTarget : spec.target = targetLabel := by
          have row : result.order.successors[label]! = #[targetLabel] := by
            simp only [getElem!_def,successors,Option.getD_some]
          have targets := spec.targets
          rw [row] at targets
          exact (List.cons.inj targets).1.symm
        have sourceRow := jump_source_row computed block jump targetIndex
        have edge : tl ∈ source[bi]!.toList := by rw [sourceRow]; simp
        have later := successor_labels (stock_lower_order run) nonempty ranked computed tag targetTag edge
        have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
        have smaller : result.order.nodes.size-targetLabel < n := by omega
        obtain ⟨targetBlock,targetFound,targetSource⟩ := block?_of_idx targetIndex
        obtain ⟨next,nextEvent,nextBlock,nextTraps⟩ := ih _ smaller targetLabel tl targetBlock rfl targetTag targetSource targetNonentry
        have demand := successor_demand run scope ranked computed
          (by simpa only [spec.atBlock] using tag)
          (by simpa only [nextBlock] using targetTag)
          (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
            s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
            SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .trapped code →
            GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
            RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.trapped code) := by
          intro fuel s ρ w func callers remaining atTerm defined returned held
          simpa only [sameTarget] using nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := Control.jump_body_traps_at run scope dominated family refines driver stable spec tag jump
          (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
          callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [jump_nonentry_prelude spec nonentry] using finished
      · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret refines driver stable env cp
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := CfgReturnAt.return_block_traps_at run scope dominated family ret refines driver stable spec
          callers remaining atTerm returned held
        simpa only [spec.noPrelude nonentry] using finished
      · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term refines driver stable env cp
        have metadata := parameter_metadata parameter dominated.ssa spec.build
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined returned held
        have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
            Nonempty (SuccessorTrap f result label bc isem MR env cp code) := by
          intro index bc selected
          obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry,forward⟩ :=
            selected_ranked_target run scope ranked tag block selected
          have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
          have smaller : result.order.nodes.size-targetLabel < n := by omega
          obtain ⟨next,member,atBlock,nextTraps⟩ :=
            ih _ smaller targetLabel tl targetBlock rfl targetTag source targetNonentry
          refine ⟨{
            index := tl
            targetLabel := targetLabel
            block := targetBlock
            event := next
            lookup := lookup
            found := found
            tag := targetTag
            member := member
            atBlock := atBlock
            forward := forward
            traps := ?_ }⟩
          intro fuel s ρ w func callers remaining atTerm defined returned held
          exact nextTraps fuel s code ρ w func callers remaining atTerm defined returned held
        have finished := spec.trapping_empty_parameter_at run scope dominated family refines driver stable
          tag term metadata.1 metadata.2 ⟨yesEmpty,noEmpty⟩ successors callers remaining atTerm
          (by simpa only [spec.atBlock] using defined) returned held
        simpa only [conditional_nonentry_prelude spec nonentry] using finished
  exact composed _ label bi b rfl tag block nonentry


end Backend.Stock.Proof.ParameterCfg

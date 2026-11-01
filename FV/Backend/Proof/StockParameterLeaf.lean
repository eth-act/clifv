import FV.Backend.Proof.StockParameterReturn
import FV.Backend.Proof.StockParameterTrap
import FV.Backend.Proof.StockConditionalTrapLeaf

/-!
# Trap leaves in parameter CFG compositions

The parameter route's return and first-trap inductions follow the actual node labels through
ranked jump blocks and parameter branches to a leaf. Here a leaf may also end in `trap`: such a
block never returns, so its return continuation is vacuous, and its first trap is
`trap_block_traps_at`. The previous predicates embed into the leaf predicates, and the previous
theorems are unchanged.
-/

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Every nonentry block jumps, returns, branches on a parameter, or ends in `trap`. -/
def NonentryParameterLeafTerms (f : Clif.Function) : Prop :=
  ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ParameterBranch f b ∨ ∃ c,b.term = .trap c

/-- Every block jumps, returns, branches on a parameter, or ends in `trap`. -/
def ParameterLeafTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ParameterBranch f b ∨ ∃ c,b.term = .trap c

theorem NonentryParameterTerms.toLeaf {f : Clif.Function} (terms : NonentryParameterTerms f) :
    NonentryParameterLeafTerms f :=
  fun bi b found nonentry => (terms bi b found nonentry).elim Or.inl
    (fun rest => Or.inr (rest.elim Or.inl (fun branch => Or.inr (Or.inl branch))))

theorem ParameterTerms.toLeaf {f : Clif.Function} (terms : ParameterTerms f) : ParameterLeafTerms f :=
  fun bi b found => (terms bi b found).elim Or.inl
    (fun rest => Or.inr (rest.elim Or.inl (fun branch => Or.inr (Or.inl branch))))

theorem parameter_leaf_terms_nonentry {f : Clif.Function} (terms : ParameterLeafTerms f) :
    NonentryParameterLeafTerms f :=
  fun bi b block _ => terms bi b block

private theorem local_family {f : Clif.Function} {b : Clif.Block} {bi : Nat}
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) (source : f.blocks[bi]? = some b) :
    ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family b (List.mem_of_getElem? source) stm member with
    (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

/-- Returns compose through jump blocks and parameter branches to return leaves; trap leaves
never return. -/
theorem nonentry_parameter_returns_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryParameterLeafTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    (env : Clif.Env) (cp : Clif.Program) {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (nonentry : bi ≠ 0) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
      ReturnsAt f result label bi b event isem MR env cp := by
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  obtain ⟨source,computed,size,bounded⟩ := stock_blockOrder_sourceTable (stock_lower_order run)
  have composed : ∀ n label bi b,result.order.nodes.size-label = n →
      result.order.nodes[label]? = some (.original bi) → f.blocks[bi]? = some b → bi ≠ 0 →
      ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi ∧
        ReturnsAt f result label bi b event isem MR env cp := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro label bi b count tag block nonentry
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
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
        obtain ⟨next,nextEvent,nextBlock,nextReturns⟩ := ih _ smaller targetLabel tl targetBlock rfl targetTag targetSource targetNonentry
        have demand := successor_demand run scope ranked computed
          (by simpa only [spec.atBlock] using tag)
          (by simpa only [nextBlock] using targetTag)
          (by simpa only [spec.atBlock,nextBlock] using edge) spec.events nextEvent spec.split
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
            s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body → s.frame.term = targetBlock.term →
            SourceDefinedAt f result.ctx tl 0 s.frame → Clif.runLoop env cp fuel s = .returned vals cm →
            GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
            RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots ⟨spec.target,0,ρ,w⟩ (.returned vals cm) := by
          intro fuel s ρ w func callers remaining atTerm defined returned held
          simpa only [sameTarget] using nextReturns fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := Control.jump_body_returns_at run scope dominated family refines driver stable spec tag jump
          (by simpa only [sameTarget] using targetTag) targetIndex targetFound nextEvent nextBlock demand continuation
          callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [jump_nonentry_prelude spec nonentry] using finished
      · obtain ⟨spec⟩ := CfgReturn.stock_lower_return_block_spec run scope dominated abi family tag block ret refines driver stable env cp
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := CfgReturnAt.return_block_returns_at run scope dominated abi family ret refines driver stable spec
          func callers remaining atTerm (by simpa only [spec.atBlock] using defined) returned held
        simpa only [spec.noPrelude nonentry] using finished
      · obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag block term refines driver stable env cp
        have metadata := parameter_metadata parameter dominated.ssa spec.build
        refine ⟨spec.core.scan,spec.events,spec.atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
            Nonempty (SuccessorReturn f result label bc isem MR env cp vals cm) := by
          intro index bc selected
          obtain ⟨tl,targetLabel,targetBlock,lookup,found,source,targetTag,targetNonentry,forward⟩ :=
            selected_ranked_target run scope ranked tag block selected
          have targetBound := (Array.getElem?_eq_some_iff.mp targetTag).1
          have smaller : result.order.nodes.size-targetLabel < n := by omega
          obtain ⟨next,member,atBlock,nextReturns⟩ :=
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
            returns := ?_ }⟩
          intro fuel s ρ w func callers remaining atTerm defined returned held
          exact nextReturns fuel s vals cm ρ w func callers remaining atTerm defined returned held
        have finished := spec.returning_empty_parameter_at run scope dominated family refines driver stable
          tag term metadata.1 metadata.2 ⟨yesEmpty,noEmpty⟩ successors callers remaining atTerm
          (by simpa only [spec.atBlock] using defined) returned held
        simpa only [conditional_nonentry_prelude spec nonentry] using finished
      · obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
          ConditionalValues.stock_lower_trap_block_code run tag block trap
        refine ⟨event,events,atBlock,?_⟩
        intro fuel s vals cm ρ w func callers remaining atTerm defined returned held
        exact absurd returned (TrapBody.trap_source_noreturn (local_family family block) (j := 0)
          (by simpa using remaining) (atTerm.trans trap))
  exact composed _ label bi b rfl tag block nonentry


/-- First traps compose through jump blocks and parameter branches; a trap leaf traps in its
body or at its terminator. -/
theorem nonentry_parameter_traps_of_leaf {f : Clif.Function} {result : Result} {rank : Nat → Nat}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) (ranked : Ranked f rank) (terms : NonentryParameterLeafTerms f)
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
      rcases terms bi b block nonentry with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,yesEmpty,noEmpty,parameter⟩ | ⟨leafCode,trap⟩
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
      · obtain ⟨event,raw,preludeCode,events,atBlock,rawCode,noPrelude,placed⟩ :=
          ConditionalValues.stock_lower_trap_block_code run tag block trap
        refine ⟨event,events,atBlock,?_⟩
        intro fuel s code ρ w func callers remaining atTerm defined trapped held
        have finished := ConditionalValues.trap_block_traps_at run scope dominated family block trap
          refines driver stable events atBlock rawCode placed remaining atTerm trapped held
        simpa only [noPrelude nonentry] using finished
  exact composed _ label bi b rfl tag block nonentry


end Backend.Stock.Proof.ParameterCfg

import FV.Backend.Proof.StockParameterArgsLeaf
import FV.Backend.Proof.StockParameterDomain
import FV.Backend.Proof.StockScalarDomainAt

/-! The ranked parameter CFG class whose parameter branches may pass block arguments satisfies the
per-successor production domain. The entry jumps, returns or branches on a parameter; nonentry
blocks may also end in `trap`. Every lowered node is an original block. -/

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Every block jumps, returns, branches on a parameter with any arguments, or ends in `trap`. -/
def ArgsParameterLeafTerms (f : Clif.Function) : Prop :=
  ∀ (bi : Nat) (b : Clif.Block),f.blocks[bi]? = some b →
    (∃ bc,b.term = .jump bc) ∨ (∃ xs,b.term = .ret xs) ∨ ArgsParameterBranch f b ∨ ∃ c,b.term = .trap c

theorem args_parameter_leaf_terms_nonentry {f : Clif.Function} (terms : ArgsParameterLeafTerms f) :
    NonentryArgsParameterLeafTerms f :=
  fun bi b block _ => terms bi b block

theorem domainAt_of_args_parameter_leaf_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : Ranked f rank) (terms : ArgsParameterLeafTerms f)
    (original : ∀ order,blockOrder f = .ok order → OriginalOrder order)
    (entryKind : ∀ b,f.blocks[0]? = some b → ∀ c,b.term ≠ .trap c)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst) : Scalar.DomainAt f := by
  have entry : ∃ (b : Clif.Block),f.blocks[0]? = some b := by
    cases blocks : f.blocks with
    | nil => exact False.elim (scope.nonempty blocks)
    | cons b rest => exact ⟨b,by simp only [blocks,List.getElem?_cons_zero]⟩
  obtain ⟨entryBlock,source⟩ := entry
  have nonentryTerms := args_parameter_leaf_terms_nonentry terms
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have order := original _ (stock_lower_order run)
    rcases terms 0 entryBlock source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,parameter⟩ | ⟨leafCode,trap⟩
    · exact args_parameter_jump_return_frame_of_leaf run scope dominated abi ranked nonentryTerms order family
        source jump entered returned refines driver memorySem stable memory arguments
    · exact parameter_return_entry_frame run scope dominated abi family source ret entered returned refines driver
        memorySem stable memory arguments
    · have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
      obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
        refines driver stable env cp
      have metadata := parameter_metadata parameter dominated.ssa spec.build
      obtain ⟨first,second,yesBlock,noBlock,labels,firstTag,secondTag⟩ :=
        spec.original_successor_labels run scope order tag source term metadata.1
      have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests entryBlock.term)[index]? = some bc →
          Nonempty (SuccessorReturn f result 0 bc isem MR env cp vals mem) := by
        intro index bc selected
        obtain ⟨tl,targetLabel,b,lookup,found,targetSource,targetTag,nonentry,forward⟩ :=
          selected_ranked_target run scope ranked tag source selected
        exact args_parameter_return_successor_of_leaf run scope dominated abi ranked nonentryTerms order family
          refines driver stable lookup found targetSource targetTag nonentry forward
      obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
      obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
        term metadata.1 metadata.2 entered driver memorySem stable memory arguments
      have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
        rw [spec.atBlock]
        exact source_defined_entry_frame dominated result.ctx entered
      have finished := spec.returning_original_parameter_at run scope dominated family refines driver stable
        tag term metadata.1 metadata.2 labels firstTag secondTag successors rfl remaining atTerm defined
        returned guarded
      exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩
    · exact False.elim (entryKind entryBlock source leafCode trap)
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have order := original _ (stock_lower_order run)
    rcases terms 0 entryBlock source with ⟨bc,jump⟩ | ⟨xs,ret⟩ | ⟨c,yes,no,term,parameter⟩ | ⟨leafCode,trap⟩
    · exact args_parameter_jump_trap_frame_of_leaf run scope dominated abi ranked nonentryTerms order family
        source jump entered trapped refines driver memorySem stable memory arguments
    · exact parameter_return_entry_trap_frame run scope dominated abi family source ret entered trapped refines
        driver memorySem stable memory arguments
    · have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
      obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
        refines driver stable env cp
      have metadata := parameter_metadata parameter dominated.ssa spec.build
      obtain ⟨first,second,yesBlock,noBlock,labels,firstTag,secondTag⟩ :=
        spec.original_successor_labels run scope order tag source term metadata.1
      have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests entryBlock.term)[index]? = some bc →
          Nonempty (SuccessorTrap f result 0 bc isem MR env cp code) := by
        intro index bc selected
        obtain ⟨tl,targetLabel,b,lookup,found,targetSource,targetTag,nonentry,forward⟩ :=
          selected_ranked_target run scope ranked tag source selected
        exact args_parameter_trap_successor_of_leaf run scope dominated abi ranked nonentryTerms order family
          refines driver stable lookup found targetSource targetTag nonentry forward
      obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
      obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
        term metadata.1 metadata.2 entered driver memorySem stable memory arguments
      have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
        rw [spec.atBlock]
        exact source_defined_entry_frame dominated result.ctx entered
      have finished := spec.trapping_original_parameter_at run scope dominated family refines driver stable
        tag term metadata.1 metadata.2 labels firstTag secondTag successors rfl remaining atTerm defined
        trapped guarded
      exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩
    · exact False.elim (entryKind entryBlock source leafCode trap)

end Backend.Stock.Proof.ParameterCfg

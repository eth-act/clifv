import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockParameterSuccessor
import FV.Backend.Proof.StockParameterReturnPrelude
import FV.Backend.Proof.StockParameterCompatibility
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.Proof.ParameterCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ConditionalValues Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

theorem domain_of_parameter_conditional_cfg {f : Clif.Function} {rank : Nat → Nat}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false)
    (ranked : Ranked f rank) (terms : ParameterTerms f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {entry : Clif.Block} {c : Nat} {yes no : Clif.BlockCall} (source : f.blocks[0]? = some entry)
    (term : entry.term = .brif c yes no) (yesEmpty : yes.args = []) (noEmpty : no.args = [])
    (parameter : ParameterCondition f c) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
      refines driver stable env cp
    have metadata := parameter_metadata parameter dominated.ssa spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests entry.term)[index]? = some bc →
        Nonempty (SuccessorReturn f result 0 bc isem MR env cp vals mem) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward⟩ :=
        selected_ranked_target run scope ranked tag source selected
      exact parameter_return_successor run scope dominated abi ranked (parameter_terms_nonentry terms) family refines driver stable
        lookup found source targetTag nonentry forward
    obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.returning_empty_parameter_at run scope dominated family refines driver stable
      tag term metadata.1 metadata.2
      ⟨yesEmpty,noEmpty⟩
      successors rfl remaining atTerm defined returned guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag source term
      refines driver stable env cp
    have metadata := parameter_metadata parameter dominated.ssa spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests entry.term)[index]? = some bc →
        Nonempty (SuccessorTrap f result 0 bc isem MR env cp code) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward⟩ :=
        selected_ranked_target run scope ranked tag source selected
      exact parameter_trap_successor run scope dominated abi ranked (parameter_terms_nonentry terms) family refines driver stable
        lookup found source targetTag nonentry forward
    obtain ⟨_,remaining,atTerm⟩ := entry_frame_parts source entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.trapping_empty_parameter_at run scope dominated family refines driver stable
      tag term metadata.1 metadata.2
      ⟨yesEmpty,noEmpty⟩
      successors rfl remaining atTerm defined trapped guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (parameter_legacy_compatible terms run scope dominated family refines driver stable env cp)⟩



end Backend.Stock.Proof.ParameterCfg

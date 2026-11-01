import FV.Backend.Proof.StockConditionalRankedCompatibility
import FV.Backend.Proof.StockConditionalRankedSuccessor
import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.ConditionalCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
private theorem selected_tail {f : Clif.Function} {result : Result}
    (shape : RankedLeafShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests shape.entry.term)[index]? = some bc) :
    ∃ tl targetLabel b,blockIdx? f bc.block = some tl ∧ f.block? bc.block = some b ∧
      f.blocks[tl]? = some b ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      tl ≠ 0 ∧ 0 < targetLabel := by
  have entryTag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨tl,middle,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope entryTag shape.source selected
  have target : ∃ (targetLabel : Nat),result.order.nodes[targetLabel]? = some (.original tl) := by
    rcases node with original | synthetic
    · exact ⟨middle,original⟩
    · obtain ⟨input,next,args,targetLabel,call,successors,tag,placed⟩ := stock_lower_critical_code run synthetic
      exact ⟨targetLabel,tag⟩
  obtain ⟨targetLabel,targetTag⟩ := target
  obtain ⟨b,found,source⟩ := block?_of_idx lookup
  have different : targetLabel ≠ 0 := by
    intro equal
    subst targetLabel
    exact nonentry (Node.original.inj (Option.some.inj (targetTag.symm.trans entryTag)))
  exact ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,Nat.pos_of_ne_zero different⟩



private theorem source_entry_parts {f : Clif.Function} (shape : RankedLeafShape f)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr) :
    fr.body = shape.entry.body ∧ fr.term = shape.entry.term := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  have source : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  cases Option.some.inj (source.symm.trans shape.source)
  exact ⟨congrArg Clif.Frame.body frame,congrArg Clif.Frame.term frame⟩

/-- The conditional source class with ranked jump tails to return or trap leaves satisfies the unchanged
universal production domain, with actual ABI entry, selected copies, return and
first-trap semantics. All compiler/DFG/choice/compatibility facts are derived. -/
theorem domain_of_ranked_leaf_shape {f : Clif.Function} (shape : RankedLeafShape f)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    have metadata := shape.condition_metadata dominated spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorReturn f result 0 bc isem MR env cp vals mem) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward⟩ :=
        selected_tail shape run scope selected
      exact SuccessorReturn.of_ranked_leaf_tail run scope dominated abi shape.ranked shape.tails shape.family refines driver stable
        lookup found source targetTag nonentry forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      shape.term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.returning_empty_parameter_at run scope dominated shape.family refines driver stable
      tag shape.term metadata.1 metadata.2
      ⟨(shape.targets shape.yes (Or.inl rfl)).1,(shape.targets shape.no (Or.inr rfl)).1⟩
      successors rfl remaining atTerm defined returned guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (shape.legacy_compatible run scope dominated spec)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    have metadata := shape.condition_metadata dominated spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorTrap f result 0 bc isem MR env cp code) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward⟩ :=
        selected_tail shape run scope selected
      exact SuccessorTrap.of_ranked_leaf_tail run scope dominated abi shape.ranked shape.tails shape.family refines driver stable
        lookup found source targetTag nonentry forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      shape.term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.trapping_empty_parameter_at run scope dominated shape.family refines driver stable
      tag shape.term metadata.1 metadata.2
      ⟨(shape.targets shape.yes (Or.inl rfl)).1,(shape.targets shape.no (Or.inr rfl)).1⟩
      successors rfl remaining atTerm defined trapped guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (shape.legacy_compatible run scope dominated spec)⟩


/-- The first compatible conditional source class satisfies the unchanged
universal production domain, with actual ABI entry, selected copies, return and
first-trap semantics. All compiler/DFG/choice/compatibility facts are derived. -/
theorem domain_of_ranked_shape {f : Clif.Function} (shape : RankedShape f)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Scalar.Domain f :=
  domain_of_ranked_leaf_shape shape.toLeaf scope dominated abi ordinary

end Backend.Stock.ConditionalCfg
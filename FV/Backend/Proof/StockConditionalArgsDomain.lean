import FV.Backend.Proof.StockConditionalArgsClass
import FV.Backend.Proof.StockConditionalArgsAt
import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockConditionalTrapLeaf
import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockScalarDomainAt

namespace Backend.Stock.ConditionalArgsCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The selected successor of an argument shape is an original return or trap block, at the
selected position of the entry's actual successor labels. -/
private theorem selected_original {f : Clif.Function} {result : Result}
    (shape : ArgsLeafShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests shape.entry.term)[index]? = some bc) :
    ∃ tl targetLabel b,blockIdx? f bc.block = some tl ∧ f.block? bc.block = some b ∧
      f.blocks[tl]? = some b ∧ result.order.successors[0]![index]? = some targetLabel ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧ tl ≠ 0 ∧ 0 < targetLabel ∧
      ((∃ xs,b.term = .ret xs) ∨ ∃ c,b.term = .trap c) := by
  have entryTag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨tl,targetLabel,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope entryTag shape.source selected
  have targetTag : result.order.nodes[targetLabel]? = some (.original tl) := by
    rcases node with original | synthetic
    · exact original
    · obtain ⟨_,same⟩ := shape.original _ (stock_lower_order run) _ _ synthetic
      cases same
  obtain ⟨b,found,source⟩ := block?_of_idx lookup
  have leaf := shape.leaves tl b source nonentry
  have different : targetLabel ≠ 0 := by
    intro equal
    subst targetLabel
    exact nonentry (Node.original.inj (Option.some.inj (targetTag.symm.trans entryTag)))
  exact ⟨tl,targetLabel,b,lookup,found,source,successor,targetTag,nonentry,
    Nat.pos_of_ne_zero different,leaf⟩

/-- The entry's actual successor labels are two original blocks. -/
private theorem successor_labels {f : Clif.Function} {result : Result}
    (shape : ArgsLeafShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result shape.entry 0 0 shape.condition shape.yes shape.no isem MR env cp)
    (parameter : result.ctx.defInst? shape.condition = none) :
    ∃ first second yesBlock noBlock,result.order.successors[0]! = #[first,second] ∧
      result.order.nodes[first]? = some (.original yesBlock) ∧
      result.order.nodes[second]? = some (.original noBlock) := by
  obtain ⟨calls,_⟩ := spec.parameter_calls shape.source shape.term parameter
  have labels : result.order.successors[0]! = #[calls.yes,calls.no] := Array.toList_inj.mp calls.labels_eq
  obtain ⟨yesBlock,first,_,_,_,_,firstSuccessor,firstTag,_⟩ :=
    selected_original shape run scope (index := 0) (bc := shape.yes) (by simp [shape.term,dests])
  obtain ⟨noBlock,second,_,_,_,_,secondSuccessor,secondTag,_⟩ :=
    selected_original shape run scope (index := 1) (bc := shape.no) (by simp [shape.term,dests])
  rw [labels] at firstSuccessor secondSuccessor
  simp only [List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.some.injEq] at firstSuccessor secondSuccessor
  subst first second
  exact ⟨calls.yes,calls.no,yesBlock,noBlock,labels,firstTag,secondTag⟩

private theorem source_entry_parts {f : Clif.Function} (shape : ArgsLeafShape f)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr) :
    fr.body = shape.entry.body ∧ fr.term = shape.entry.term := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  have source : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  cases Option.some.inj (source.symm.trans shape.source)
  exact ⟨congrArg Clif.Frame.body frame,congrArg Clif.Frame.term frame⟩

/-- The conditional class whose branch passes block arguments to return or trap leaves
satisfies the per-successor production domain, with actual ABI entry, selected copies of the
actual argument vectors, return and first-trap semantics. All compiler facts are derived. -/
theorem domainAt_of_argsLeafShape {f : Clif.Function} (shape : ArgsLeafShape f)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Scalar.DomainAt f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    have metadata := shape.condition_metadata dominated spec.build
    obtain ⟨first,second,yesBlock,noBlock,labels,firstTag,secondTag⟩ :=
      successor_labels shape run scope spec metadata.1
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorReturn f result 0 bc isem MR env cp vals mem) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,_,targetTag,nonentry,forward,⟨xs,ret⟩ | ⟨c,trap⟩⟩ :=
        selected_original shape run scope selected
      · exact SuccessorReturn.of_return_block run scope dominated abi shape.family refines driver stable
          lookup found source targetTag ret nonentry forward
      · exact SuccessorReturn.of_trap_block run shape.family lookup found source targetTag trap forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      shape.term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.returning_original_parameter_at run scope dominated shape.family refines driver
      stable tag shape.term metadata.1 metadata.2 labels firstTag secondTag
      successors rfl remaining atTerm defined returned guarded
    exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    have metadata := shape.condition_metadata dominated spec.build
    obtain ⟨first,second,yesBlock,noBlock,labels,firstTag,secondTag⟩ :=
      successor_labels shape run scope spec metadata.1
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorTrap f result 0 bc isem MR env cp code) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,_,targetTag,nonentry,forward,⟨xs,ret⟩ | ⟨c,trap⟩⟩ :=
        selected_original shape run scope selected
      · exact SuccessorTrap.of_return_block run scope dominated abi shape.family refines driver stable
          lookup found source targetTag ret nonentry forward
      · exact SuccessorTrap.of_trap_block run scope dominated shape.family refines driver stable
          lookup found source targetTag trap nonentry forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := conditional_entry_prelude run scope dominated spec
      shape.term metadata.1 metadata.2 entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.trapping_original_parameter_at run scope dominated shape.family refines driver
      stable tag shape.term metadata.1 metadata.2 labels firstTag secondTag
      successors rfl remaining atTerm defined trapped guarded
    exact ⟨entrySeed spec.core.scan.ctx fr,RunOkABIAt.prefix path finished⟩

end Backend.Stock.ConditionalArgsCfg

import FV.Backend.Proof.StockComparisonZeroCompatibility
import FV.Backend.Proof.StockComparisonZeroAt
import FV.Backend.Proof.StockConditionalLeaf
import FV.Backend.Proof.StockConditionalTrapLeaf
import FV.Backend.Proof.StockScalarContract

namespace Backend.Stock.ComparisonZeroCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The selected successor of a leaf shape is an original return or trap block. -/
private theorem selected_leaf_block {f : Clif.Function} {result : Result}
    (shape : LeafShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests shape.entry.term)[index]? = some bc) :
    ∃ tl targetLabel b,blockIdx? f bc.block = some tl ∧ f.block? bc.block = some b ∧
      f.blocks[tl]? = some b ∧ result.order.nodes[targetLabel]? = some (.original tl) ∧
      tl ≠ 0 ∧ 0 < targetLabel ∧ ((∃ xs,b.term = .ret xs) ∨ ∃ c,b.term = .trap c) := by
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
  obtain ⟨params,leaf⟩ := shape.leaves tl b source nonentry
  have different : targetLabel ≠ 0 := by
    intro equal
    subst targetLabel
    exact nonentry (Node.original.inj (Option.some.inj (targetTag.symm.trans entryTag)))
  exact ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,Nat.pos_of_ne_zero different,leaf⟩

private theorem source_entry_parts {f : Clif.Function} (shape : LeafShape f)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr) :
    fr.body = shape.entry.body ∧ fr.term = shape.entry.term := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  have source : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  cases Option.some.inj (source.symm.trans shape.source)
  exact ⟨congrArg Clif.Frame.body frame,congrArg Clif.Frame.term frame⟩

/-- The zero comparison source class with return or trap leaves satisfies
the unchanged universal production domain, with actual ABI entry, the real
`cbz`/`cbnz` branch, selected copies, return and first-trap semantics. All
compiler/DFG/choice/compatibility facts are derived. -/
theorem domain_of_leafShape {f : Clif.Function} (shape : LeafShape f)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Scalar.Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    obtain ⟨cc,ty,x,y,wide,ty',k,origin,typeX,parameterX,constY,equality,zero⟩ :=
      shape.condition_metadata dominated spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorReturn f result 0 bc isem MR env cp vals mem) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward,⟨xs,ret⟩ | ⟨c,trap⟩⟩ :=
        selected_leaf_block shape run scope selected
      · exact SuccessorReturn.of_return_block run scope dominated abi shape.family refines driver stable
          lookup found source targetTag ret nonentry forward
      · exact SuccessorReturn.of_trap_block run shape.family lookup found source targetTag trap forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := comparison_zero_entry_prelude run scope dominated spec
      shape.term origin wide typeX parameterX constY equality zero entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.returning_empty_comparison_zero_at run scope dominated shape.family refines driver stable
      tag shape.term origin wide typeX parameterX constY equality zero
      ⟨(shape.targets shape.yes (Or.inl rfl)).1,(shape.targets shape.no (Or.inr rfl)).1⟩
      successors rfl remaining atTerm defined returned guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (shape.legacy_compatible run scope dominated spec)⟩
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable world memory arguments
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated shape.family tag shape.source shape.term
      refines driver stable env cp
    obtain ⟨cc,ty,x,y,wide,ty',k,origin,typeX,parameterX,constY,equality,zero⟩ :=
      shape.condition_metadata dominated spec.build
    have successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests shape.entry.term)[index]? = some bc →
        Nonempty (SuccessorTrap f result 0 bc isem MR env cp code) := by
      intro index bc selected
      obtain ⟨tl,targetLabel,b,lookup,found,source,targetTag,nonentry,forward,⟨xs,ret⟩ | ⟨c,trap⟩⟩ :=
        selected_leaf_block shape run scope selected
      · exact SuccessorTrap.of_return_block run scope dominated abi shape.family refines driver stable
          lookup found source targetTag ret nonentry forward
      · exact SuccessorTrap.of_trap_block run scope dominated shape.family refines driver stable
          lookup found source targetTag trap nonentry forward
    obtain ⟨remaining,atTerm⟩ := source_entry_parts shape entered
    obtain ⟨ρ,w,path,guarded,values,sameWorld⟩ := comparison_zero_entry_prelude run scope dominated spec
      shape.term origin wide typeX parameterX constY equality zero entered driver memorySem stable memory arguments
    have defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 fr := by
      rw [spec.atBlock]
      exact source_defined_entry_frame dominated result.ctx entered
    have finished := spec.trapping_empty_comparison_zero_at run scope dominated shape.family refines driver stable
      tag shape.term origin wide typeX parameterX constY equality zero
      ⟨(shape.targets shape.yes (Or.inl rfl)).1,(shape.targets shape.no (Or.inr rfl)).1⟩
      successors rfl remaining atTerm defined trapped guarded
    have whole := RunOkABIAt.prefix path finished
    exact ⟨entrySeed spec.core.scan.ctx fr,whole.legacyCompatible (shape.legacy_compatible run scope dominated spec)⟩

private theorem normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- Original source checks and the zero comparison selector derive the
unchanged production contract. Returns/traps, ABI entry and compatibility are
internal. -/
theorem domain_of_leafEligible {f : Clif.Function} (eligible : leafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  obtain ⟨shape⟩ := leafEligible_shape eligible
  have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
    apply List.find?_eq_none.mpr
    intro p member
    simp [(normal_abi shape.abiParams) p member]
  have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
    rw [sigRets,noSret]
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
    simpa [(normal_abi shape.abiReturns) p member] using sret
  exact domain_of_leafShape shape scope dominated abi ordinary

theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_leafEligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,sourceOk_sound source,rfl,lowered⟩

end Backend.Stock.ComparisonZeroCfg

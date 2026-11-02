import FV.Backend.Lowering.StockConditionalArgsRankedCfg
import FV.Backend.Proof.StockConditionalArgsClass
import FV.Backend.Proof.StockConditionalArgsAt
import FV.Backend.Proof.StockConditionalRankedSuccessor
import FV.Backend.Proof.StockConditionalEntryPrelude
import FV.Backend.Proof.StockScalarCodeDomain

/-! The argument-passing conditional class with ranked forward tails: the entry `brif` may pass
block arguments, and every other block jumps forward, returns or ends in `trap`. It satisfies the
per-successor production domain; its checked split code has the code domain. -/

namespace Backend.Stock.ConditionalArgsCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Proof.ConditionalValues
  Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source facts for the ranked argument-passing class. -/
structure RankedArgsShape (f : Clif.Function) where
  entry : Clif.Block
  condition : Nat
  yes : Clif.BlockCall
  no : Clif.BlockCall
  source : f.blocks[0]? = some entry
  term : entry.term = .brif condition yes no
  parameter : ∃ ty,(condition,ty) ∈ entry.params ∧ (ty = .i32 ∨ ty = .i64)
  tails : NonentryJumpLeafBlocks f
  ranked : Ranked f id
  family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst
  abiParams : f.sig.params.all Scalar.narrowAbiEligible = true
  abiReturns : f.sig.returns.all Scalar.narrowAbiEligible = true
  original : ∀ order,blockOrder f = .ok order → ∀ (label : Nat) (node : Node),
    order.nodes[label]? = some node → ∃ bi,node = .original bi

private theorem later_sound {f : Clif.Function} {bc : Clif.BlockCall}
    (checked : laterTarget f bc = true) : ∃ tl,blockIdx? f bc.block = some tl ∧ 0 < tl := by
  unfold laterTarget at checked
  cases lookup : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [lookup] at checked; cases checked
  | some tl =>
    simp only [lookup,decide_eq_true_eq] at checked
    exact ⟨tl,lookup,checked⟩

private theorem control_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : Backend.Stock.ForwardCfg.controlEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) := by
  cases term <;> simp only [Backend.Stock.ForwardCfg.controlEligible] at checked
  case jump bc =>
    cases target : f.blocks.findIdx? (·.id == bc.block) with
    | none => simp only [target] at checked; cases checked
    | some ti =>
      simp only [target,decide_eq_true_eq] at checked
      exact Or.inl ⟨bc,ti,rfl,target,checked⟩
  case ret xs => exact Or.inr ⟨xs,rfl⟩
  all_goals cases checked

private theorem control_leaf_sound {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : Backend.Stock.ForwardCfg.controlLeafEligible f bi term = true) :
    (∃ bc target,term = .jump bc ∧ f.blocks.findIdx? (·.id == bc.block) = some target ∧ bi < target) ∨
      (∃ xs,term = .ret xs) ∨ (∃ c,term = .trap c) := by
  cases term
  case trap c => exact Or.inr (Or.inr ⟨c,rfl⟩)
  all_goals
    rcases control_sound (by simpa only [Backend.Stock.ForwardCfg.controlLeafEligible] using checked) with jump | ret
    · exact Or.inl jump
    · exact Or.inr (Or.inl ret)

/-- The executable selector derives its source facts. -/
theorem rankedLeafEligible_shape {f : Clif.Function} (checked : rankedLeafEligible f = true) :
    Nonempty (RankedArgsShape f) := by
  cases blocks : f.blocks with
  | nil => simp [rankedLeafEligible,blocks] at checked
  | cons entry rest =>
    cases term : entry.term <;> simp only [rankedLeafEligible,blocks,term] at checked
    case brif c yes no =>
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨parameter,yesGood⟩,noGood⟩,tails⟩,bodies⟩,params⟩,returns⟩,ordered⟩ := checked
      obtain ⟨pair,member,good⟩ := List.any_eq_true.mp parameter
      obtain ⟨value,ty⟩ := pair
      change (value == c && (ty == .i32 || ty == .i64)) = true at good
      simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at good
      obtain ⟨same,wide⟩ := good
      subst value
      have atControl : ∀ bi b,f.blocks[bi]? = some b → bi ≠ 0 →
          Backend.Stock.ForwardCfg.controlLeafEligible f bi b.term = true := by
        intro bi b found nonentry
        cases bi with
        | zero => exact False.elim (nonentry rfl)
        | succ bi =>
          rw [blocks,List.getElem?_cons_succ] at found
          exact List.all_eq_true.mp tails (b,bi) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
      refine ⟨{
        entry := entry
        condition := c
        yes := yes
        no := no
        source := by simp only [blocks,List.getElem?_cons_zero]
        term := term
        parameter := ⟨ty,member,wide⟩
        tails := ?_
        ranked := ?_
        family := ?_
        abiParams := params
        abiReturns := returns
        original := originalOrder_sound ordered }⟩
      · intro bi b found nonentry
        rcases control_leaf_sound (atControl bi b found nonentry) with ⟨bc,ti,jump,lookup,less⟩ | ret | trap
        · exact Or.inl ⟨bc,jump⟩
        · exact Or.inr (Or.inl ret)
        · exact Or.inr (Or.inr trap)
      · intro bi b ti destination found present target
        change bi < ti
        by_cases isEntry : bi = 0
        · subst bi
          have same : b = entry := Option.some.inj (found.symm.trans (by simp only [blocks,List.getElem?_cons_zero]))
          subst b
          simp only [term,destinations,List.mem_cons,List.not_mem_nil,or_false] at present
          rcases present with rfl | rfl
          · obtain ⟨tl,lookup,less⟩ := later_sound yesGood
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · obtain ⟨tl,lookup,less⟩ := later_sound noGood
            have same : tl = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
        · rcases control_leaf_sound (atControl bi b found isEntry) with ⟨bc,next,jump,lookup,less⟩ | ⟨xs,ret⟩ | ⟨c,trap⟩
          · simp only [jump,destinations,List.mem_singleton] at present
            subst destination
            have same : next = ti := Option.some.inj (lookup.symm.trans target)
            simpa only [same] using less
          · simp only [ret,destinations] at present; cases present
          · simp only [trap,destinations] at present; cases present
      · intro b member stm present
        have member' : b ∈ entry :: rest := by simpa only [blocks] using member
        exact Scalar.maskMixedBodyEligible_sound
          (List.all_eq_true.mp (List.all_eq_true.mp bodies b member') stm present)
    all_goals cases checked

theorem RankedArgsShape.condition_metadata {f : Clif.Function} (shape : RankedArgsShape f)
    (dominated : Dominated f) {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    ctx.defInst? shape.condition = none ∧
      (ctx.valueType? shape.condition = some (.int 32) ∨ ctx.valueType? shape.condition = some (.int 64)) := by
  obtain ⟨original,st,oldBuild,spec,view⟩ := buildCtx_source build
  obtain ⟨ty,parameter,wide⟩ := shape.parameter
  have parameterId : shape.condition ∈ shape.entry.params.map (·.1) :=
    List.mem_map.mpr ⟨(shape.condition,ty),parameter,rfl⟩
  have noDefinition := defInst_par spec.facts dominated.ssa shape.source parameterId
  have originalType := (spec.facts.types dominated.ssa).2 shape.entry (List.mem_of_getElem? shape.source)
    (shape.condition,ty) parameter
  refine ⟨?_,?_⟩
  · simpa only [Ctx.defInst?,view.valDef] using noDefinition
  · have typed : ctx.valueType? shape.condition = some (CTy.ofClif ty) := by
      simpa only [Ctx.valueType?,view.valTy] using originalType
    rcases wide with rfl | rfl
    · exact Or.inl typed
    · exact Or.inr typed

private theorem selected_original {f : Clif.Function} {result : Result}
    (shape : RankedArgsShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests shape.entry.term)[index]? = some bc) :
    ∃ tl targetLabel b,blockIdx? f bc.block = some tl ∧ f.block? bc.block = some b ∧
      f.blocks[tl]? = some b ∧ result.order.successors[0]![index]? = some targetLabel ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧ tl ≠ 0 ∧ 0 < targetLabel := by
  have entryTag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨tl,targetLabel,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope entryTag shape.source selected
  have targetTag : result.order.nodes[targetLabel]? = some (.original tl) := by
    rcases node with original | synthetic
    · exact original
    · obtain ⟨_,same⟩ := shape.original _ (stock_lower_order run) _ _ synthetic
      cases same
  obtain ⟨b,found,source⟩ := block?_of_idx lookup
  have different : targetLabel ≠ 0 := by
    intro equal
    subst targetLabel
    exact nonentry (Node.original.inj (Option.some.inj (targetTag.symm.trans entryTag)))
  exact ⟨tl,targetLabel,b,lookup,found,source,successor,targetTag,nonentry,Nat.pos_of_ne_zero different⟩

private theorem successor_labels {f : Clif.Function} {result : Result}
    (shape : RankedArgsShape f) (run : Stock.lower f = .ok result) (scope : LowerScope f)
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

private theorem source_entry_parts {f : Clif.Function} (shape : RankedArgsShape f)
    {args : List Clif.Val} {fr : Clif.Frame} (entered : SourceEntry f args fr) :
    fr.body = shape.entry.body ∧ fr.term = shape.entry.term := by
  obtain ⟨b,regs,entry,types,paramTypes,set,frame⟩ := entered
  have source : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  cases Option.some.inj (source.symm.trans shape.source)
  exact ⟨congrArg Clif.Frame.body frame,congrArg Clif.Frame.term frame⟩

/-- The ranked argument-passing class satisfies the per-successor production domain. -/
theorem domainAt_of_rankedArgsShape {f : Clif.Function} (shape : RankedArgsShape f)
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
      obtain ⟨tl,targetLabel,b,lookup,found,source,_,targetTag,nonentry,forward⟩ :=
        selected_original shape run scope selected
      exact SuccessorReturn.of_ranked_leaf_tail run scope dominated abi shape.ranked shape.tails shape.family
        refines driver stable lookup found source targetTag nonentry forward
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
      obtain ⟨tl,targetLabel,b,lookup,found,source,_,targetTag,nonentry,forward⟩ :=
        selected_original shape run scope selected
      exact SuccessorTrap.of_ranked_leaf_tail run scope dominated abi shape.ranked shape.tails shape.family
        refines driver stable lookup found source targetTag nonentry forward
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

private theorem normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

theorem domainAt_of_rankedLeafEligible {f : Clif.Function} (eligible : rankedLeafEligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) :
    Scalar.DomainAt f := by
  obtain ⟨shape⟩ := rankedLeafEligible_shape eligible
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
  exact domainAt_of_rankedArgsShape shape scope dominated abi ordinary

theorem rankedSourceOk_sound {f : Clif.Function} (checked : rankedSourceOk f = true) :
    Scalar.DomainAt f := by
  simp only [rankedSourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domainAt_of_rankedLeafEligible eligible (lowerScope_of scope) (dominated_of dominated) abi

/-- The executable check derives the code domain of the published split code. -/
theorem rankedCheck_sound {f : Clif.Function} {vc : VCode} (checked : rankedCheck f vc = true) :
    Scalar.CodeDomain f vc := by
  simp only [rankedCheck,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run] at lowered
    cases splitRun : splitEdgesChecked result.code result.edgeArgs with
    | error message => simp [splitRun] at lowered
    | ok split =>
      simp only [splitRun,decide_eq_true_eq] at lowered
      subst vc
      exact (rankedSourceOk_sound source).code run splitRun

end Backend.Stock.ConditionalArgsCfg

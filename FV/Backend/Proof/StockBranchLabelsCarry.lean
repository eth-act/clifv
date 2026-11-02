import FV.Backend.Proof.StockComparisonArgsCarryBounded

/-! Branch compositions from the successor labels (#140, CB-13).

`returning/trapping_selected_carry_below_of_core` (T7b-9) take the named call packet of ordinary
`brif` (3231) only for its two successor labels. A branch on a one-bit condition is selected by
`tbnz` or `tbz` (3251, 3257) and has no such packet. Here `selected_arguments_demanded_of_labels`,
`selected_argument_values_of_labels` and `returning/trapping_selected_carry_below_of_labels` take
the two labels (`result.order.successors[label]!.toList = [yesLabel,noLabel]`) instead. The proofs
are those of T7b-9. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Backend.Stock.Proof.Control
  Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.ForwardSource
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm branchArgs emitBranch collectOutgoing scanBlock lowerBlockCore

private theorem marks_size (xs : List Nat) (st : State) :
    (xs.foldl State.mark st).demand.size = st.demand.size := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.foldl_cons,State.mark,Array.size_modify] using ih (st.mark x)

private theorem mapped_member {ctx : Ctx} {xs : List Nat} {rs : List Reg}
    (mapped : xs.mapM ctx.valueReg? = some rs) {x : Nat} (member : x ∈ xs) :
    ∃ r,ctx.valueReg? x = some r := by
  induction xs generalizing rs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at mapped
    obtain ⟨r,lookup,tail,rest,rfl⟩ := mapped
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨r,lookup⟩
    · exact ih rest member

private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers,usersN,args,view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0,view.valDef,bytes,args]
  simp only [availIn,inFix_eq,users,bytes,work,view.valDef]

/-- `selected_arguments_demanded_of_calls` from the two successor labels of the branch, which every
conditional branch rule produces: every source argument of a
selected successor is demanded after the body, at an original or a critical-edge successor. -/
theorem ConditionalBodySpec.selected_arguments_demanded_of_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (packet : ∃ yesLabel noLabel,result.order.successors[label]!.toList = [yesLabel,noLabel])
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {x : Nat} (member : x ∈ bc.args) : Demanded spec.term.output.state x := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have func := (buildCtx_mappedInv scope spec.build).func
  have terminal : spec.term ∈ spec.core.scan.output.records := by
    rw [spec.split.records]
    exact List.mem_cons_self ..
  have recordSize := Extent.lower_record_demand_size run spec.core.scan spec.events spec.term terminal
  obtain ⟨tl,targetLabel,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag source selected
  -- the value is mapped, so it is in bounds of every demand array of the run
  have inBounds : ∀ (regs : List Reg),bc.args.mapM result.ctx.valueReg? = some regs →
      x < result.ctx.valTy.size := by
    intro regs mapping
    obtain ⟨r,mapped⟩ := mapped_member mapping member
    have currentMap : spec.core.scan.ctx.valueReg? x = some r := by
      rw [(stock_lower_record_context run scope spec.events).2.1 x]
      exact mapped
    have bound := (Extent.lower_mapped_demand_bounds run scope spec.events terminal currentMap).1
    rw [recordSize.1] at bound
    exact bound
  rcases node with original | edge
  · -- the branch's own outgoing collection marks the arguments
    obtain ⟨yesLabel,noLabel,pair⟩ := packet
    have labels : result.order.successors[label]! = #[yesLabel,noLabel] := Array.toList_inj.mp pair
    have coreRun := spec.coreRun
    rw [labels] at coreRun
    obtain ⟨emission,afterEdges,_,_,outgoing,scanInput,_,branchFlag,_⟩ :=
      conditional_core_calls term coreRun
    obtain ⟨middle,middleEither,firstOriginal,nextEither,secondOriginal⟩ :=
      stock_collect_conditional_marks_any func source term outgoing
    have outputDemand := (stock_branch_scan_body_code spec.split branchFlag).2
    have afterSize : afterEdges.demand.size = result.ctx.valTy.size := by
      have := recordSize.1
      rw [spec.split.termInput,scanInput] at this
      exact this
    have middleSize : afterEdges.demand.size = middle.demand.size := by
      rcases nextEither with same | same <;> simp only [same,marks_size]
    have emissionSize : middle.demand.size = emission.state.demand.size := by
      rcases middleEither with same | same <;> simp only [same,marks_size]
    have nodeTag : result.order.nodes[targetLabel]! = .original tl := by simp [getElem!_def,original]
    have demandedAfter : Demanded afterEdges x := by
      cases index with
      | zero =>
        have same : yesLabel = targetLabel := by
          rw [labels] at successor
          simpa using successor
        subst same
        have selectedEq : yes = bc := by simpa [term,dests] using selected
        subst selectedEq
        obtain ⟨middleEq,regs,mapping⟩ := firstOriginal tl nodeTag
        have bound := inBounds regs mapping
        have emissionBound : x < emission.state.demand.size := by omega
        have middleBound : x < middle.demand.size := by omega
        have marked : Demanded middle x := by
          rw [middleEq]
          exact (demanded_markList_iff _ _ x emissionBound).mpr (Or.inl member)
        rcases nextEither with same | same
        · rw [same]; exact marked
        · rw [same]
          exact (demanded_markList_iff _ _ x middleBound).mpr (Or.inr marked)
      | succ index =>
        cases index with
        | zero =>
          have same : noLabel = targetLabel := by
            rw [labels] at successor
            simpa using successor
          subst same
          have selectedEq : no = bc := by simpa [term,dests] using selected
          subst selectedEq
          obtain ⟨nextEq,regs,mapping⟩ := secondOriginal tl nodeTag
          have bound := inBounds regs mapping
          have middleBound : x < middle.demand.size := by omega
          rw [nextEq]
          exact (demanded_markList_iff _ _ x middleBound).mpr (Or.inl member)
        | succ index => simp [term,dests] at selected
    unfold Demanded at demandedAfter ⊢
    rw [outputDemand,spec.split.termInput,scanInput]
    exact demandedAfter
  · -- the edge node marks the arguments before the predecessor is scanned
    have later := stock_lower_edge_after_pred run scope tag edge
    have bounded := (Array.getElem?_eq_some_iff.mp edge).1
    have edgeTag : result.order.nodes[targetLabel]! = .edge bi index tl := by simp [getElem!_def,edge]
    have secondTag : result.order.nodes[label]! = .original spec.core.scan.block := by
      simp [getElem!_def,tag,spec.atBlock]
    obtain ⟨input,size,⟨regs,mapping⟩,flow⟩ := ordered_edge_demand_of_labels run scope bounded later
      edgeTag secondTag spec.events spec.split source selected
    have bound : x < input.demand.size := by rw [size]; exact inBounds regs mapping
    have marked := (demanded_markList_iff input bc.args x bound).mpr (Or.inl member)
    unfold Demanded at marked ⊢
    have := flow x
    omega

/-- `selected_argument_values_of_calls` from the two successor labels of the branch: a guarded post-body frame
holds the source arguments of a selected successor, at an original or a critical-edge
successor. -/
theorem ConditionalBodySpec.selected_argument_values_of_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (packet : ∃ yesLabel noLabel,result.order.successors[label]!.toList = [yesLabel,noLabel])
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc) :
    ValuesHeld (fun x => x ∈ bc.args) result.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨original,st0,oldBuild,_,view⟩ := buildCtx_source spec.build
  have choice : bc = yes ∨ bc = no := by simpa [term,dests] using List.mem_of_getElem? selected
  intro x member v read
  have either : x ∈ yes.args ∨ x ∈ no.args :=
    choice.elim (fun same => Or.inl (same ▸ member)) (fun same => Or.inr (same ▸ member))
  have available := (dominated.uses original spec.ranges st0 oldBuild bi b source).2 x
    (by rcases either with inside | inside <;> simp [term,abiTerm,Driver.termArgs,inside])
  have available' : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    rw [spec.atBlock,view_avail view f]
    exact available
  obtain ⟨n,mapped,value⟩ := held.2.2.2 x
    ⟨spec.selected_arguments_demanded_of_labels run scope tag term packet selected member,available'⟩ v read
  refine ⟨n,?_,value⟩
  rw [← (stock_lower_record_context run scope spec.events).2.1 x]
  exact mapped

/-- `returning_selected_carry_below_of_core` from the two successor labels of the branch and the
conclusion of a carry core: the selected successor may take arguments, through an original or a
critical-edge successor, and continues below the block's fuel from `CarryRel` of its own carry
set. -/
theorem ConditionalBodySpec.returning_selected_carry_below_of_labels
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (packet : ∃ yesLabel noLabel,result.order.successors[label]!.toList = [yesLabel,noLabel])
    {carry : Nat → Prop} {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : ReturningCarryCore spec carry fuel s vals cm ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ := core
  let bc := if Clif.Sem.truthy value.bits then yes else no
  let choice := if Clif.Sem.truthy value.bits then 0 else 1
  have selected : (dests b.term)[choice]? = some bc := by
    cases truth : Clif.Sem.truthy value.bits <;> simp [dests,termShape,choice,bc,truth]
  obtain ⟨next⟩ := successors choice bc selected
  have nextBlock : next.event.block = sourceTargetIndex f bc := by
    simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
  have arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx t.frame
      (fun key => regs (aliasNum result.final.alias key)) :=
    spec.selected_argument_values_of_labels run scope dominated tag termShape packet post.1 selected
  have carriedAvailable : ∀ x,next.carried x →
      x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
    intro x kept
    rw [next.atBlock]
    exact next.available x kept
  have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
      next.carried spec.term.output.state carry := by
    rw [next.atBlock]
    simp only [sourceTargetParams,next.found,Option.getD_some]
    exact next.cover
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
      carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left (by omega) {t with frame := fr} ρnext endWorld
    nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
      (spec.raw.insts.map (·.mapRegs resolve)).size := by
    simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
    omega
  have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
  have whole := RunOkABIAt.prefix path finished
  simpa only [slotEq] using whole

/-- `trapping_selected_carry_below_of_core` from the two successor labels of the branch and the
conclusion of a carry core. -/
theorem ConditionalBodySpec.trapping_selected_carry_below_of_labels
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brif c yes no) (packet : ∃ yesLabel noLabel,result.order.successors[label]!.toList = [yesLabel,noLabel])
    {carry : Nat → Prop} {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : TrappingCarryCore spec carry fuel s trapCode ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) := by
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (spec.core.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < spec.core.code.size := by simpa using hk
    simp only [spec.rawCode,Array.map_append]
    rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    simp [bound]
  rcases core with failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩
  · obtain ⟨offset,i,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failed
    obtain ⟨path,bound,instruction,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
    exact ⟨label,spec.preludeCode.size+offset,regs,prefixWorld,_,i,ops,outs,endWorld,path,
      spec.placed,instruction,operands,semantics,coded⟩
  · let bc := if Clif.Sem.truthy value.bits then yes else no
    let choice := if Clif.Sem.truthy value.bits then 0 else 1
    have selected : (dests b.term)[choice]? = some bc := by
      cases truth : Clif.Sem.truthy value.bits <;> simp [dests,termShape,choice,bc,truth]
    obtain ⟨next⟩ := successors choice bc selected
    have nextBlock : next.event.block = sourceTargetIndex f bc := by
      simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
    have arguments : ValuesHeld (fun x => x ∈ bc.args) result.ctx t.frame
        (fun key => regs (aliasNum result.final.alias key)) :=
      spec.selected_argument_values_of_labels run scope dominated tag termShape packet post.1 selected
    have carriedAvailable : ∀ x,next.carried x →
        x ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
      intro x kept
      rw [next.atBlock]
      exact next.available x kept
    have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
        next.carried spec.term.output.state carry := by
      rw [next.atBlock]
      simp only [sourceTargetParams,next.found,Option.getD_some]
      exact next.cover
    obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
      spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
        carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
    have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
    subst tl
    have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
      (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
    subst targetLabel
    obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = next.block := by
      rw [post.1.1] at found
      exact Option.some.inj (found.symm.trans next.found)
    have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
    have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
    have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := next.traps left (by omega) {t with frame := fr} ρnext endWorld
      nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
    have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
        (spec.raw.insts.map (·.mapRegs resolve)).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
      omega
    have path := route.execute run scope driver.toDriverSemG spec.placed segment machine endPosition
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotEq] using whole

end Backend.Stock.Proof.ConditionalValues

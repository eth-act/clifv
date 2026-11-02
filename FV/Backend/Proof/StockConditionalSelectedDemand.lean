import FV.Backend.Proof.StockConditionalArgumentDemand
import FV.Backend.Proof.StockCfgTraversalScans
import FV.Backend.Proof.StockCfgTraversalDemand
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.StockEdgeOrder
import FV.Backend.Proof.StockDemandExtent
import FV.Backend.Proof.StockConditionalBodyCalls
import FV.Backend.Proof.StockSelectedGraph

/-! The source arguments of a conditional branch's selected successor are demanded after the body
and held by a guarded post-body frame, whether the successor is an original block or a
critical-edge node. An original successor's arguments are marked by the branch's own outgoing
collection. A critical edge's arguments are marked by the edge node, which the backward
traversal lowers before its predecessor. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Backend.Stock.Proof.Control
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

/-- One outgoing collection step for a branch successor at an original node marks the selected
arguments; at an edge node it changes nothing. -/
private theorem outgoing_step_marks {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (source : f.blocks[bi]? = some b) {order : Order}
    {label j : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[j]? = some bc)
    {input next : State} {acc acc' : Array (Array Reg)}
    (run : outgoingStep ctx order bi (input,acc) (label,j) = .ok (next,acc')) :
    (∀ t,order.nodes[label]! = .original t → next = bc.args.foldl State.mark input ∧
      ∃ regs : List Reg,bc.args.mapM ctx.valueReg? = some regs) ∧
      (next = input ∨ next = bc.args.foldl State.mark input) := by
  unfold outgoingStep at run
  cases node : order.nodes[label]! with
  | edge pred k target =>
    simp only [node,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
    refine ⟨fun t same => (by cases same),Or.inl run.1.symm⟩
  | original t =>
    simp only [node] at run
    cases call : branchArgs ctx input bi j with
    | error message => simp only [call,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,state⟩ := pair
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,-⟩ := run
      have marked := stock_branchArgs_selected_marks func source selected call
      exact ⟨fun _ _ => ⟨marked,args.toList,stock_branchArgs_selected_mapping func source selected call⟩,
        Or.inr marked⟩

/-- Outgoing collection over a conditional's two successors marks the arguments of each successor
at an original node. -/
theorem stock_collect_conditional_marks_any {ctx : Ctx} {f : Clif.Function}
    (func : ctx.func = f) {bi c : Nat} {b : Clif.Block} {yes no : Clif.BlockCall}
    (source : f.blocks[bi]? = some b) (term : b.term = .brif c yes no) {order : Order}
    {first second : Nat} {input next : State} {outgoing : Array (Array Reg)}
    (run : collectOutgoing ctx order bi #[first,second] input = .ok (next,outgoing)) :
    ∃ middle : State,(middle = input ∨ middle = yes.args.foldl State.mark input) ∧
      (∀ t,order.nodes[first]! = .original t → middle = yes.args.foldl State.mark input ∧
        ∃ regs : List Reg,yes.args.mapM ctx.valueReg? = some regs) ∧
      (next = middle ∨ next = no.args.foldl State.mark middle) ∧
      (∀ t,order.nodes[second]! = .original t → next = no.args.foldl State.mark middle ∧
        ∃ regs : List Reg,no.args.mapM ctx.valueReg? = some regs) := by
  simp only [collectOutgoing] at run
  change ([(first,0),(second,1)] : List (Nat × Nat)).foldlM (outgoingStep ctx order bi)
    (input,#[]) = .ok (next,outgoing) at run
  simp only [List.foldlM_cons,List.foldlM_nil] at run
  cases step0 : outgoingStep ctx order bi (input,#[]) (first,0) with
  | error message => simp only [step0,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨middle,acc⟩ := pair
    simp only [step0,bind,Except.bind] at run
    cases step1 : outgoingStep ctx order bi (middle,acc) (second,1) with
    | error message => simp only [step1] at run; cases run
    | ok pair =>
      obtain ⟨state,acc'⟩ := pair
      simp only [step1,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,-⟩ := run
      obtain ⟨firstOriginal,firstEither⟩ :=
        outgoing_step_marks func source (bc := yes) (by simp [term,dests]) step0
      obtain ⟨secondOriginal,secondEither⟩ :=
        outgoing_step_marks func source (bc := no) (by simp [term,dests]) step1
      exact ⟨middle,firstEither,firstOriginal,secondEither,secondOriginal⟩

/-- The edge node lowering marks the selected arguments of its predecessor's branch. -/
theorem edge_node_marks {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order} {f : Clif.Function}
    {params : List Nat} {label pred k target : Nat} {input output : DriverState}
    (func : ctx.func = f) (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .edge pred k target) {pb : Clif.Block} {bc : Clif.BlockCall}
    (source : f.blocks[pred]? = some pb) (selected : (dests pb.term)[k]? = some bc) :
    output.state = bc.args.foldl State.mark input.state ∧
      ∃ regs : List Reg,bc.args.mapM ctx.valueReg? = some regs := by
  unfold lowerNode at run
  simp only [node] at run
  cases called : branchArgs ctx input.state pred k with
  | error message => simp only [called,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨args,next⟩ := pair
    simp only [called,bind,Except.bind,pure,Except.pure] at run
    cases run
    exact ⟨stock_branchArgs_selected_marks func source selected called,args.toList,
      stock_branchArgs_selected_mapping func source selected called⟩

private theorem fold_scan_mem {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    {event : BlockScanEvent} (member : event ∈ input.blockScans.toList) :
    event ∈ output.blockScans.toList := by
  induction labels generalizing input with
  | nil => simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run; subst output; exact member
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,called,rest⟩ := Except.bind_ok run
    obtain ⟨added,scans,_⟩ := CfgTrace.node_scan_append called
    exact ih rest (by rw [scans]; exact List.mem_append_left _ member)

private theorem fold_demand_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.state.demand.size = input.state.demand.size := by
  induction labels generalizing input with
  | nil => simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run; subst output; rfl
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,called,rest⟩ := Except.bind_ok run
    exact (ih rest).trans (Extent.lowerNode_demand_size called)

/-- A critical-edge node lowered before a later-scanned block marks its selected arguments into
that block's terminator demand, in the actual traversal. -/
theorem ordered_edge_demand {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {earlier intervening suffix : List Nat} {edgeLabel secondLabel pred k target : Nat}
    {second : BlockScanEvent} {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (labels : (Array.range result.order.nodes.size).reverse.toList =
      earlier ++ edgeLabel :: (intervening ++ secondLabel :: suffix))
    (edgeTag : result.order.nodes[edgeLabel]! = .edge pred k target)
    (secondTag : result.order.nodes[secondLabel]! = .original second.block)
    (sm : second ∈ result.blockScans.toList) (split : SourceBodySplit f second b term body)
    {pb : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[pred]? = some pb)
    (selected : (dests pb.term)[k]? = some bc) :
    ∃ input : State,input.demand.size = result.ctx.valTy.size ∧
      (∃ regs : List Reg,bc.args.mapM result.ctx.valueReg? = some regs) ∧
      ∀ x : Nat,(bc.args.foldl State.mark input).demand[x]! ≤ term.output.state.demand[x]! := by
  obtain ⟨ranges,params,starting,finishing,build,ordered,initial,empty,folded,events⟩ :=
    LinearCfg.actual_traversal run
  rw [labels,List.foldlM_append] at folded
  obtain ⟨before,prefixRun,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_cons] at rest
  obtain ⟨afterEdge,edgeRun,rest⟩ := Except.bind_ok rest
  rw [List.foldlM_append] at rest
  obtain ⟨beforeSecond,interveningRun,rest⟩ := Except.bind_ok rest
  rw [List.foldlM_cons] at rest
  obtain ⟨afterSecond,secondRun,suffixRun⟩ := Except.bind_ok rest
  have func := (buildCtx_mappedInv scope build).func
  obtain ⟨marked,mapping⟩ := edge_node_marks func edgeRun edgeTag source selected
  obtain ⟨secondData,sc,secondCore,secondState,secondScans⟩ := LinearCfg.original_node_scan secondRun secondTag
  have so := stock_lowerBlockCore_scanOrigin secondCore
  have scm : sc.scan ∈ result.blockScans.toList := by
    have inAfter : sc.scan ∈ afterSecond.blockScans.toList := by simp [secondScans]
    simpa only [events] using fold_scan_mem suffixRun inAfter
  have seq : second = sc.scan := CfgTrace.actual_scan_unique run scope sm scm so.2.2.1.symm
  have through := CfgDemand.traversal_demand_mono interveningRun
  have beforeCore := (CfgDemand.core_demand_mono secondCore).1
  have terminal := CfgDemand.instruction_demand_mono split.termRun
  have secondInput : sc.scan.input = term.input := by rw [← seq,split.termInput]
  have size : before.state.demand.size = result.ctx.valTy.size := by
    rw [fold_demand_size prefixRun,initial]
    exact buildCtx_demand_size build
  refine ⟨before.state,size,mapping,fun x => ?_⟩
  rw [← marked]
  exact Nat.le_trans (through x) (Nat.le_trans (by simpa only [secondInput] using beforeCore x) (terminal x))

/-- The label form: a critical edge after its predecessor in the block order. -/
theorem ordered_edge_demand_of_labels {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {edgeLabel secondLabel pred k target : Nat}
    {second : BlockScanEvent} {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (bounded : edgeLabel < result.order.nodes.size) (before : secondLabel < edgeLabel)
    (edgeTag : result.order.nodes[edgeLabel]! = .edge pred k target)
    (secondTag : result.order.nodes[secondLabel]! = .original second.block)
    (sm : second ∈ result.blockScans.toList) (split : SourceBodySplit f second b term body)
    {pb : Clif.Block} {bc : Clif.BlockCall} (source : f.blocks[pred]? = some pb)
    (selected : (dests pb.term)[k]? = some bc) :
    ∃ input : State,input.demand.size = result.ctx.valTy.size ∧
      (∃ regs : List Reg,bc.args.mapM result.ctx.valueReg? = some regs) ∧
      ∀ x : Nat,(bc.args.foldl State.mark input).demand[x]! ≤ term.output.state.demand[x]! := by
  have edgeMember : edgeLabel ∈ (Array.range result.order.nodes.size).reverse.toList := by
    simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using bounded
  obtain ⟨earlier,rest,labels⟩ := List.append_of_mem edgeMember
  have remaining := (stock_backward_suffix_split labels).2
  have secondMember : secondLabel ∈ rest := by
    rw [remaining]
    simpa only [Array.toList_reverse,Array.toList_range,List.mem_reverse,List.mem_range] using before
  obtain ⟨intervening,suffix,restEq⟩ := List.append_of_mem secondMember
  rw [restEq] at labels
  exact ordered_edge_demand run scope labels edgeTag secondTag sm split source selected

/-- Every source argument of a selected successor of a conditional on a parameter is demanded
after the body, at an original or a critical-edge successor. -/
theorem ConditionalBodySpec.selected_arguments_demanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
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
    obtain ⟨calls,_⟩ := spec.parameter_calls source term parameter
    have labels : result.order.successors[label]! = #[calls.yes,calls.no] := Array.toList_inj.mp calls.labels_eq
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
        have same : calls.yes = targetLabel := by
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
          have same : calls.no = targetLabel := by
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

/-- A guarded post-body frame holds the source arguments of a selected successor, at an original
or a critical-edge successor. -/
theorem ConditionalBodySpec.selected_argument_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
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
    ⟨spec.selected_arguments_demanded run scope tag term parameter selected member,available'⟩ v read
  refine ⟨n,?_,value⟩
  rw [← (stock_lower_record_context run scope spec.events).2.1 x]
  exact mapped

end Backend.Stock.Proof.ConditionalValues

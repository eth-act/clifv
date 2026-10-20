import FV.Backend.Proof.StockCriticalEdgeArity
import FV.Backend.Proof.StockEdgeArity
import FV.Backend.Proof.PerEdgeSpillCycleFixture
import FV.Backend.Proof.StockOutgoingShapeWitness

namespace Backend.Stock.Proof.GraphArityWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private theorem cycle_order : blockOrder IndexedSpillFixture.function = .ok {
    nodes := #[.original 0,.original 1,.edge 1 0 1,.original 2],successors := #[#[1],#[2,3],#[1],#[]]} := by cbv
private theorem try_order (indirect : Bool) : blockOrder (SpillEntryFixture.function indirect) = .ok {
    nodes := #[.original 0,.original 1,.original 2],successors := #[#[2,1],#[],#[]]} := by cases indirect <;> cbv

/-- Complete checked cyclic Stock lowering inhabits original indexed-successor
selection, critical-source provenance and exact critical-edge arity. Its real
critical vector has two live arguments; raw preparation, checked fallback and
physical lowering succeed. -/
theorem stock_graph_critical_arity_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (targetLabel : Nat) (tb : VBlock) (args : Array Reg),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      result.order.nodes[2]? = some (.edge 1 0 1) ∧
      (∃ (b : Clif.Block) (id : Nat) (sourceArgs : List Clif.TryArg) (target : Nat),
        IndexedSpillFixture.function.blocks[1]? = some b ∧ (destinations b.term)[0]? = some (id,sourceArgs) ∧
        IndexedSpillFixture.function.blocks.findIdx? (·.id == id) = some target ∧
        (result.order.nodes[2]? = some (.original target) ∨ result.order.nodes[2]? = some (.edge 1 0 target))) ∧
      (∃ (b : Clif.Block) (id : Nat) (sourceArgs : List Clif.TryArg),
        IndexedSpillFixture.function.blocks[1]? = some b ∧ (destinations b.term)[0]? = some (id,sourceArgs) ∧
        IndexedSpillFixture.function.blocks.findIdx? (·.id == id) = some 1) ∧
      result.order.successors[2]? = some #[targetLabel] ∧ result.order.nodes[targetLabel]? = some (.original 1) ∧
      result.code.blocks[targetLabel]? = some tb ∧ result.edgeArgs[2]? = some #[args] ∧
      args.size = tb.params.size ∧ args.size = 2 ∧
      (∃ ss ps,result.code.cfg = .ok (ss,ps) ∧ EdgeArityAt result.code result.edgeArgs ss) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,raw,fallback,accepted,physical,rest⟩
  obtain ⟨_,ss,ps,cfg,_⟩ := PerEdgePrep.prepareAt_input_facts raw
  have allArity := stock_lower_edge_arity run scope dominated.ssa ss ps cfg
  have order := Except.ok.inj ((stock_lower_order run).symm.trans cycle_order)
  have critical : result.order.nodes[2]? = some (.edge 1 0 1) := by rw [order]; rfl
  have original : result.order.nodes[1]? = some (.original 1) := by rw [order]; rfl
  have row : result.order.successors[1]? = some #[2,3] := by rw [order]; rfl
  have selected := stock_lower_indexed_successor_origin run original row (j := 0) (targetLabel := 2) rfl
  have source := stock_lower_critical_source run critical
  obtain ⟨targetLabel,tb,args,successors,targetNode,targetBlock,outgoing,arity⟩ :=
    stock_lower_critical_edge_arity run scope dominated.ssa critical
  obtain ⟨block,placed,_,params⟩ := stock_lower_original_block_params run scope dominated.ssa targetNode
    (b := IndexedSpillFixture.function.blocks[1]!) (by rfl) (by decide)
  rw [targetBlock] at placed
  cases placed
  have targetSize : tb.params.size = 2 := by
    rw [params]
    simp [edgeParamNumbers,IndexedSpillFixture.function]
  exact ⟨result,p,rf,af,targetLabel,tb,args,run,scope,dominated,arityOk_of (by decide +kernel),critical,selected,source,
    successors,targetNode,targetBlock,outgoing,arity,arity.trans targetSize,⟨ss,ps,cfg,allArity⟩,raw,fallback,accepted,physical⟩

/-- Complete direct/indirect TryCall normal and handler paths inhabit the
original indexed-successor theorem and the reservation-independent successful
collector arity theorem. The complete source pipelines also pass checked
fallback allocation and physical lowering. -/
theorem stock_graph_try_arity_witness (indirect handler : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (args : Array Reg) (next : State),
      Stock.lower (SpillEntryFixture.function indirect) = .ok result ∧
      LowerScope (SpillEntryFixture.function indirect) ∧ Dominated (SpillEntryFixture.function indirect) ∧
      ArityOk (SpillEntryFixture.function indirect) ∧
      (∃ (b : Clif.Block) (id : Nat) (sourceArgs : List Clif.TryArg) (target : Nat),
        (SpillEntryFixture.function indirect).blocks[0]? = some b ∧
        (destinations b.term)[SpillEntryFixture.index handler]? = some (id,sourceArgs) ∧
        (SpillEntryFixture.function indirect).blocks.findIdx? (·.id == id) = some target ∧
        (result.order.nodes[SpillEntryFixture.target handler]? = some (.original target) ∨
         result.order.nodes[SpillEntryFixture.target handler]? = some (.edge 0 (SpillEntryFixture.index handler) target))) ∧
      branchArgs result.ctx result.initial 0 (SpillEntryFixture.index handler) = .ok (args,next) ∧
      (∃ (id : Nat) (sourceArgs : List Clif.TryArg) (target : Clif.Block),
        (destinations result.ctx.func.blocks[0]!.term)[SpillEntryFixture.index handler]? = some (id,sourceArgs) ∧
        result.ctx.func.block? id = some target ∧ args.size = target.params.length) ∧
      (∃ ss ps,result.code.cfg = .ok (ss,ps) ∧ EdgeArityAt result.code result.edgeArgs ss) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af := by
  obtain ⟨result,p,rf,af,ranges,args,next,run,scope,dominated,arity,build,classes,call,same,shape,target,frame,
    raw,fallback,accepted,physical⟩ := OutgoingShapeWitness.stock_outgoing_shape_witness indirect handler
  obtain ⟨_,ss,ps,cfg,_⟩ := PerEdgePrep.prepareAt_input_facts raw
  have allArity := stock_lower_edge_arity run scope dominated.ssa ss ps cfg
  have order := Except.ok.inj ((stock_lower_order run).symm.trans (try_order indirect))
  have node : result.order.nodes[0]? = some (.original 0) := by rw [order]; rfl
  have row : result.order.successors[0]? = some #[2,1] := by rw [order]; rfl
  have edge : (#[2,1] : Array Nat)[SpillEntryFixture.index handler]? = some (SpillEntryFixture.target handler) := by cases handler <;> rfl
  exact ⟨result,p,rf,af,args,next,run,scope,dominated,arity,stock_lower_indexed_successor_origin run node row edge,
    call,stock_branchArgs_target_arity call,⟨ss,ps,cfg,allArity⟩,raw,fallback,accepted,physical⟩

end Backend.Stock.Proof.GraphArityWitness

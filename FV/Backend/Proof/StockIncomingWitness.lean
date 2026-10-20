import FV.Backend.Proof.StockSharedSource
import FV.Backend.Proof.StockCriticalSplitWitness
import FV.Backend.Proof.PerEdgeSpillCycleFixture

namespace Backend.Stock.Proof.IncomingWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
private theorem cycle_order : blockOrder IndexedSpillFixture.function = .ok {
    nodes := #[.original 0,.original 1,.edge 1 0 1,.original 2],successors := #[#[1],#[2,3],#[1],#[]]} := by cbv
private theorem cycle_source : stockSourceTable IndexedSpillFixture.function = .ok #[#[1],#[1,2],#[]] := by cbv
private theorem try_order (indirect : Bool) : blockOrder (CriticalSplitFixture.function indirect) = .ok {
    nodes := #[.original 0,.edge 0 0 1,.original 1],successors := #[#[1],#[2],#[]]} := by cases indirect <;> cbv

/-- Complete checked cyclic Stock lowering inhabits full original/critical
node uniqueness, both actual incoming loop-edge provenance branches, the
unique actual exit edge from source indegree1, and original shared-target
source-jump classification. Original source and every pipeline stage remain. -/
theorem stock_incoming_cycle_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (source : Array (Array Nat)),
      Stock.lower IndexedSpillFixture.function = .ok result ∧ LowerScope IndexedSpillFixture.function ∧
      Dominated IndexedSpillFixture.function ∧ ArityOk IndexedSpillFixture.function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.order.nodes.toList.Nodup ∧
      (∀ label,result.order.nodes[label]? = some (.edge 1 0 1) → label = 2) ∧
      stockSourceTable IndexedSpillFixture.function = .ok source ∧
      IncomingOriginalAt result source 1 0 0 ∧ IncomingOriginalAt result source 1 2 0 ∧
      (∀ (b j : Nat) (row : Array Nat),result.order.successors[b]? = some row → row[j]? = some 3 → b = 1 ∧ j = 1) ∧
      (∃ (block : Clif.Block) (dest : Clif.BlockCall),IndexedSpillFixture.function.blocks[0]? = some block ∧ block.term = .jump dest) ∧
      SharedSourceAt IndexedSpillFixture.function result 1 0 ∧ SharedSourceAt IndexedSpillFixture.function result 1 2 := by
  obtain ⟨fixture⟩ := IndexedSpillFixture.cycle_fixture
  rcases fixture with ⟨result,p,rf,af,run,scope,dominated,raw,fallback,accepted,physical,rest⟩
  have order := Except.ok.inj ((stock_lower_order run).symm.trans cycle_order)
  have nonempty : IndexedSpillFixture.function.blocks.length ≠ 0 := by decide
  have critical : result.order.nodes[2]? = some (.edge 1 0 1) := by rw [order]; rfl
  have loopNode : result.order.nodes[1]? = some (.original 1) := by rw [order]; rfl
  have firstRow : result.order.successors[0]? = some #[1] := by rw [order]; rfl
  have criticalRow : result.order.successors[2]? = some #[1] := by rw [order]; rfl
  obtain ⟨source,computed,incoming⟩ := stock_lower_incoming_original run
  have first := incoming 1 1 loopNode 0 0 #[1] firstRow rfl
  have second := incoming 1 1 loopNode 2 0 #[1] criticalRow rfl
  obtain ⟨source',degree,computed',counted,unique⟩ := stock_lower_low_degree_incoming_unique run scope
  have same := Except.ok.inj (computed.symm.trans computed')
  subst source'
  have sourceEq := Except.ok.inj (computed.symm.trans cycle_source)
  have degreeComputed : sourceIndegree source IndexedSpillFixture.function.blocks.length = .ok #[0,2,1] := by
    rw [sourceEq]; cbv
  have degreeEq := Except.ok.inj (counted.symm.trans degreeComputed)
  have exitUnique : ∀ (b j : Nat) (row : Array Nat),result.order.successors[b]? = some row → row[j]? = some 3 → b = 1 ∧ j = 1 := by
    intro b j row atRow atEdge
    exact unique 3 2 (by rw [order]; rfl) (by rw [degreeEq]; decide) b j 1 1 row #[2,3]
      atRow atEdge (by rw [order]; rfl) rfl
  have sourceJump := stock_lower_shared_direct_source_jump run scope loopNode
    (b := 0) (bi := 0) (j := 0) (b₂ := 2) (j₂ := 0) (by rw [order]; rfl)
    firstRow rfl criticalRow rfl (by exact .inl (by decide))
  exact ⟨result,p,rf,af,source,run,scope,dominated,arityOk_of (by decide +kernel),raw,fallback,accepted,physical,
    stock_lower_nodes_nodup run scope,
    fun label tag => stock_blockOrder_node_unique (stock_lower_order run) nonempty tag critical,
    computed,first,second,exitUnique,sourceJump,
    stock_lower_shared_source_kind run scope (j := 0) (j₂ := 0) firstRow rfl criticalRow rfl (.inl (by decide)),
    stock_lower_shared_source_kind run scope (j := 0) (j₂ := 0) criticalRow rfl firstRow rfl (.inl (by decide))⟩

/-- Complete direct/indirect forced one-successor TryCall sources inhabit
critical-node uniqueness and exact incoming provenance for the synthetic jump
into the original return target. The unreachable source predecessor and all
original conditions/raw/checked/physical stages are retained. -/
theorem stock_incoming_single_try_witness (indirect : Bool) :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (source : Array (Array Nat)),
      Stock.lower (CriticalSplitFixture.function indirect) = .ok result ∧ LowerScope (CriticalSplitFixture.function indirect) ∧
      Dominated (CriticalSplitFixture.function indirect) ∧ ArityOk (CriticalSplitFixture.function indirect) ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      result.order.nodes.toList.Nodup ∧ stockSourceTable (CriticalSplitFixture.function indirect) = .ok source ∧
      IncomingOriginalAt result source 1 1 0 ∧
      (∀ label,result.order.nodes[label]? = some (.edge 0 0 1) → label = 1) ∧
      (∀ (b j : Nat) (row : Array Nat),result.order.successors[b]? = some row → row[j]? = some 1 → b = 0 ∧ j = 0) := by
  obtain ⟨result,p,rf,af,source,degree,run,scope,dominated,arity,raw,fallback,accepted,physical,sourceRun,sourceEq,counted,
    degreeEq,complete,single,shared,absent,critical,criticalAt,firstRow,secondRow,counts⟩ :=
    CriticalSplitWitness.stock_single_try_forced_split_witness indirect
  have order := Except.ok.inj ((stock_lower_order run).symm.trans (try_order indirect))
  obtain ⟨source',computed,incoming⟩ := stock_lower_incoming_original run
  have same := Except.ok.inj (sourceRun.symm.trans computed)
  subst source'
  have actual := incoming 2 1 (by rw [order]; rfl) 1 0 #[2] secondRow rfl
  have nonempty : (CriticalSplitFixture.function indirect).blocks.length ≠ 0 := by cases indirect <;> decide
  exact ⟨result,p,rf,af,source,run,scope,dominated,arity,raw,fallback,accepted,physical,
    stock_lower_nodes_nodup run scope,sourceRun,actual,
    fun label tag => stock_blockOrder_node_unique (stock_lower_order run) nonempty tag criticalAt,
    fun b j row atRow atEdge => stock_lower_critical_incoming_unique run scope criticalAt atRow atEdge firstRow rfl⟩

end Backend.Stock.Proof.IncomingWitness

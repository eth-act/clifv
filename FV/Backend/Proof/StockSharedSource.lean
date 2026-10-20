import FV.Backend.Proof.StockIncomingDegree

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem unforced_single_source {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi : Nat}
    (single : source[bi]!.size = 1) (unforced : forceCritical f.blocks[bi]!.term = false) :
    ∃ (b : Clif.Block) (dest : Clif.BlockCall),f.blocks[bi]? = some b ∧ b.term = .jump dest := by
  obtain ⟨row,atRow⟩ : ∃ row,source[bi]? = some row := by
    cases found : source[bi]? with
    | none => simp only [getElem!_def,found] at single; cases single
    | some row => exact ⟨row,rfl⟩
  have biBound : bi < f.blocks.length := by
    have bound := (Array.getElem?_eq_some_iff.mp atRow).1
    rw [(stock_sourceTable_bounds computed).1] at bound
    exact bound
  have block : f.blocks[bi]? = some f.blocks[bi] := List.getElem?_eq_getElem biBound
  have bang : f.blocks[bi]! = f.blocks[bi] := by rw [getElem!_def,block]
  rw [bang] at unforced
  unfold stockSourceTable at computed
  obtain ⟨out,mapped,atOut⟩ := (array_mapM_ok computed).2 bi f.blocks[bi] (by simpa using block)
  rw [atRow] at atOut
  cases atOut
  have length := (array_mapM_ok mapped).1
  have rowSize : row.size = 1 := by simpa only [getElem!_def,atRow,Option.getD_some] using single
  simp only [List.size_toArray] at length
  cases term : f.blocks[bi].term with
  | jump dest => exact ⟨f.blocks[bi],dest,block,term⟩
  | brif c t e => simp only [term,destinations,List.length_cons,List.length_nil] at length; omega
  | brTable index dest table => simp only [term,forceCritical] at unforced; cases unforced
  | tryCall fn args table => simp only [term,forceCritical] at unforced; cases unforced
  | tryCallIndirect fn args table => simp only [term,forceCritical] at unforced; cases unforced
  | ret values => simp only [term,destinations,List.length_nil] at length; omega
  | trap code => simp only [term,destinations,List.length_nil] at length; omega
  | returnCall fn args => simp only [term,destinations,List.length_nil] at length; omega

/-- An original Stock node that still branches directly to an original target
with two distinct actual incoming indexed edges must be an original source
jump. Forced one-successor TryCall/brTable and multi-successor forms cannot
remain direct: actual insertion completeness and source indegree exclude them.
This classifies source terminators; emitted/prepared instruction transport is
proved separately. -/
theorem stock_lower_shared_direct_source_jump {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel target b bi j b₂ j₂ : Nat} {ss ss₂ : Array Nat}
    (targetNode : result.order.nodes[targetLabel]? = some (.original target))
    (sourceNode : result.order.nodes[b]? = some (.original bi))
    (row : result.order.successors[b]? = some ss) (edge : ss[j]? = some targetLabel)
    (otherRow : result.order.successors[b₂]? = some ss₂) (otherEdge : ss₂[j₂]? = some targetLabel)
    (distinct : b ≠ b₂ ∨ j ≠ j₂) :
    ∃ (block : Clif.Block) (dest : Clif.BlockCall),f.blocks[bi]? = some block ∧ block.term = .jump dest := by
  obtain ⟨source,degree,computed,counted,complete⟩ := stock_lower_critical_split_complete run
  obtain ⟨source',degree',computed',counted',unique⟩ := stock_lower_low_degree_incoming_unique run scope
  have same := Except.ok.inj (computed.symm.trans computed')
  subst source'
  have sameDegree := Except.ok.inj (counted.symm.trans counted')
  subst degree'
  have high : 1 < degree[target]! := by
    apply Classical.byContradiction
    intro notHigh
    have same := unique targetLabel target targetNode (by omega) b j b₂ j₂ ss ss₂ row edge otherRow otherEdge
    rcases distinct with different | different
    · exact different same.1
    · exact different same.2
  obtain ⟨source',computed',incoming⟩ := stock_lower_incoming_original run
  have same := Except.ok.inj (computed.symm.trans computed')
  subst source'
  rcases incoming targetLabel target targetNode b j ss row edge with ⟨bi',tag,selected,absent⟩ | ⟨bi',k,tag,_,_⟩
  · have same := Node.original.inj (Option.some.inj (sourceNode.symm.trans tag))
    subst bi'
    have notForced : ¬(forceCritical f.blocks[bi]!.term || decide (1 < source[bi]!.size)) = true := by
      intro forced
      exact absent (complete bi (Array.mem_toList_iff.mpr (Array.mem_of_getElem? sourceNode)) j target selected forced high)
    have unforced : forceCritical f.blocks[bi]!.term = false := by
      cases actual : forceCritical f.blocks[bi]!.term with
      | false => rfl
      | true => exact False.elim (notForced (by simp only [actual,Bool.true_or]))
    have single : source[bi]!.size = 1 := by
      have bound := (Array.getElem?_eq_some_iff.mp selected).1
      have small : ¬1 < source[bi]!.size := fun big => notForced (by simp [big])
      omega
    exact unforced_single_source computed single unforced
  · rw [sourceNode] at tag
    cases tag

/-- Structural source classification at an actual shared graph target. -/
def SharedSourceAt (f : Clif.Function) (result : Result) (targetLabel b : Nat) : Prop :=
  ∃ target,result.order.nodes[targetLabel]? = some (.original target) ∧
    ((∃ (bi : Nat) (block : Clif.Block) (dest : Clif.BlockCall),result.order.nodes[b]? = some (.original bi) ∧
        f.blocks[bi]? = some block ∧ block.term = .jump dest) ∨
     ∃ bi k,result.order.nodes[b]? = some (.edge bi k target))

/-- Every source of an actual shared Stock graph target is either an original
source jump or an inserted critical node. Target kind and exact source-node
lookups are derived from actual incoming edges, not caller certificates. -/
theorem stock_lower_shared_source_kind {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel b j b₂ j₂ : Nat} {ss ss₂ : Array Nat}
    (row : result.order.successors[b]? = some ss) (edge : ss[j]? = some targetLabel)
    (otherRow : result.order.successors[b₂]? = some ss₂) (otherEdge : ss₂[j₂]? = some targetLabel)
    (distinct : b ≠ b₂ ∨ j ≠ j₂) :
    SharedSourceAt f result targetLabel b := by
  obtain ⟨target,targetNode⟩ := stock_lower_shared_target_original run scope row edge otherRow otherEdge distinct
  obtain ⟨source,_,incoming⟩ := stock_lower_incoming_original run
  refine ⟨target,targetNode,?_⟩
  rcases incoming targetLabel target targetNode b j ss row edge with ⟨bi,sourceNode,_,_⟩ | ⟨bi,k,sourceNode,_,_⟩
  · obtain ⟨block,dest,sourceBlock,jump⟩ := stock_lower_shared_direct_source_jump run scope targetNode sourceNode
      row edge otherRow otherEdge distinct
    exact .inl ⟨bi,block,dest,sourceNode,sourceBlock,jump⟩
  · exact .inr ⟨bi,k,sourceNode⟩

end Backend.Stock.Proof

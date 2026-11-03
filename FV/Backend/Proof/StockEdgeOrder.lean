import FV.Backend.Proof.StockGraphEdges
import FV.Backend.Proof.StockSourceOrder

/-! In Stock's block order, every critical-edge node comes after its predecessor's original node:
`blockOrder` pushes a block's edge nodes right after the block itself. The backward traversal
therefore lowers an edge node before its predecessor. -/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option maxRecDepth 20000

/-- Every edge node has its predecessor's original node at an earlier index. -/
private def EdgesAfter (nodes : Array Node) : Prop :=
  ∀ (e pred index target : Nat),nodes[e]? = some (.edge pred index target) →
    ∃ l < e,nodes[l]? = some (.original pred)

/-- The original node of block `bi` is present. -/
private def Present (bi : Nat) (nodes : Array Node) : Prop :=
  ∃ l < nodes.size,nodes[l]? = some (.original bi)

private def edgeStep (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes : Array Node) :
    Except String (ForInStep (Array Node)) :=
  if indegree[pair.1]! > 1 then pure (.yield (nodes.push (.edge bi pair.2 pair.1))) else pure (.yield nodes)
private def forceTerm : Clif.Terminator → Bool
  | .brTable .. | .tryCall .. | .tryCallIndirect .. => true
  | _ => false
private def nodeStep (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes : Array Node) : Except String (ForInStep (Array Node)) := do
  let nodes := nodes.push (.original bi)
  if forceTerm f.blocks[bi]!.term || source[bi]!.size > 1 then
    let next ← forIn source[bi]!.zipIdx nodes (edgeStep indegree bi)
    pure (.yield next)
  else pure (.yield nodes)

private theorem push_keeps {nodes : Array Node} {i : Nat} {node x : Node}
    (found : nodes[i]? = some node) : (nodes.push x)[i]? = some node := by
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  rw [Array.getElem?_push]
  simp only [show i ≠ nodes.size by omega,ite_false,found]

private theorem push_after {nodes : Array Node} {x : Node} (valid : EdgesAfter nodes)
    (new : ∀ pred index target,x = .edge pred index target → ∃ l < nodes.size,nodes[l]? = some (.original pred)) :
    EdgesAfter (nodes.push x) := by
  intro e pred index target found
  rw [Array.getElem?_push] at found
  split at found
  · rename_i last
    subst last
    obtain ⟨l,less,old⟩ := new pred index target (Option.some.inj found)
    exact ⟨l,less,push_keeps old⟩
  · obtain ⟨l,less,old⟩ := valid e pred index target found
    exact ⟨l,less,push_keeps old⟩

private theorem present_push {bi : Nat} {nodes : Array Node} {x : Node} (present : Present bi nodes) :
    Present bi (nodes.push x) := by
  obtain ⟨l,less,old⟩ := present
  exact ⟨l,by simp only [Array.size_push]; omega,push_keeps old⟩

private theorem edge_after {indegree : Array Nat} {bi : Nat} {pair : Nat × Nat} {nodes next : Array Node}
    (state : EdgesAfter nodes ∧ Present bi nodes)
    (run : edgeStep indegree bi pair nodes = .ok (.yield next)) : EdgesAfter next ∧ Present bi next := by
  unfold edgeStep at run
  split at run <;> cases run
  · refine ⟨push_after state.1 ?_,present_push state.2⟩
    intro pred index target same
    cases same
    exact state.2
  · exact state

private theorem edge_not_done (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes next : Array Node) :
    edgeStep indegree bi pair nodes ≠ .ok (.done next) := by
  unfold edgeStep
  split <;> simp [pure,Except.pure]

private theorem node_after {f : Clif.Function} {source : Array (Array Nat)} {indegree : Array Nat}
    {bi : Nat} {nodes next : Array Node} (valid : EdgesAfter nodes)
    (run : nodeStep f source indegree bi nodes = .ok (.yield next)) : EdgesAfter next := by
  have pushed : EdgesAfter (nodes.push (.original bi)) := push_after valid (fun _ _ _ same => by cases same)
  have present : Present bi (nodes.push (.original bi)) :=
    ⟨nodes.size,by simp only [Array.size_push]; omega,by simp⟩
  unfold nodeStep at run
  dsimp only at run
  split at run
  · obtain ⟨out,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    exact (Prep.forIn_inv (edgeStep indegree bi) source[bi]!.zipIdx.toList
      (fun _ nodes => EdgesAfter nodes ∧ Present bi nodes)
      (fun _ _ _ _ _ state step => edge_after state step)
      (edge_not_done indegree bi) _ _ ⟨pushed,present⟩ loop).1
  · cases run
    exact pushed

private theorem node_not_done (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source indegree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨out,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]

/-- Every edge node of the actual block order has its predecessor's original node earlier. -/
theorem stock_blockOrder_edge_after {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order)
    {e pred index target : Nat} (found : order.nodes[e]? = some (.edge pred index target)) :
    ∃ l < e,order.nodes[l]? = some (.original pred) := by
  unfold blockOrder at run
  simp only [bind,Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    split at run
    · cases run
    · rename_i indegree degreeRun
      split at run
      · cases run
      · rename_i nodes nodesRun
        have loop : forIn (rpo source) #[] (nodeStep f source indegree) = .ok nodes := by
          apply Eq.trans ?_ nodesRun
          congr 2
        rw [← Array.forIn_toList] at loop
        have valid : EdgesAfter nodes := Prep.forIn_inv (nodeStep f source indegree) _
          (fun _ nodes => EdgesAfter nodes)
          (fun _ _ _ _ _ valid step => node_after valid step)
          (node_not_done f source indegree) _ _ (by intro e pred index target found; simp at found) loop
        split at run
        · cases run
        · cases run
          exact valid e pred index target found

/-- In the actual lowering, a selected critical edge's node label is after its predecessor's
original label. -/
theorem stock_lower_edge_after_pred {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi e index target : Nat}
    (tag : result.order.nodes[label]? = some (.original bi))
    (edge : result.order.nodes[e]? = some (.edge bi index target)) : label < e := by
  obtain ⟨l,less,original⟩ := stock_blockOrder_edge_after (stock_lower_order run) edge
  have same := stock_blockOrder_original_unique (stock_lower_order run)
    (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) tag original
  omega

end Backend.Stock.Proof

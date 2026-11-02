import FV.Backend.Proof.StockForwardSourceOrder
import FV.Backend.Proof.StockOrderGraph

namespace Backend.Stock.Proof.CriticalOwners
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private def forceTerm : Clif.Terminator → Bool
  | .brTable .. | .tryCall .. | .tryCallIndirect .. => true
  | _ => false
private def Owners (f : Clif.Function) (source : Array (Array Nat)) (nodes : Array Node) : Prop :=
  ∀ pred index target,Node.edge pred index target ∈ nodes.toList →
    forceTerm f.blocks[pred]!.term = true ∨ 1 < source[pred]!.size
private def edgeStep (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes : Array Node) :
    Except String (ForInStep (Array Node)) :=
  if indegree[pair.1]! > 1 then pure (.yield (nodes.push (.edge bi pair.2 pair.1))) else pure (.yield nodes)
private def nodeStep (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes : Array Node) : Except String (ForInStep (Array Node)) := do
  let nodes := nodes.push (.original bi)
  if forceTerm f.blocks[bi]!.term || source[bi]!.size > 1 then
    let next ← forIn source[bi]!.zipIdx nodes (edgeStep indegree bi)
    pure (.yield next)
  else pure (.yield nodes)

private theorem push_original {f : Clif.Function} {source : Array (Array Nat)} {nodes : Array Node}
    (valid : Owners f source nodes) (bi : Nat) : Owners f source (nodes.push (.original bi)) := by
  intro pred index target member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | same
  · exact valid pred index target old
  · cases same
private theorem edge_valid {f : Clif.Function} {source : Array (Array Nat)} {indegree : Array Nat} {bi : Nat}
    {pair : Nat × Nat} {nodes next : Array Node} (valid : Owners f source nodes)
    (owner : forceTerm f.blocks[bi]!.term = true ∨ 1 < source[bi]!.size)
    (run : edgeStep indegree bi pair nodes = .ok (.yield next)) : Owners f source next := by
  unfold edgeStep at run
  split at run <;> cases run
  · intro pred index target member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact valid pred index target old
    · cases same; exact owner
  · exact valid
private theorem edge_not_done (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes next : Array Node) :
    edgeStep indegree bi pair nodes ≠ .ok (.done next) := by
  unfold edgeStep
  split <;> simp [pure,Except.pure]
private theorem node_valid {f : Clif.Function} {source : Array (Array Nat)} {indegree : Array Nat}
    {bi : Nat} {nodes next : Array Node} (valid : Owners f source nodes)
    (run : nodeStep f source indegree bi nodes = .ok (.yield next)) : Owners f source next := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · rename_i condition
    have owner : forceTerm f.blocks[bi]!.term = true ∨ 1 < source[bi]!.size := by
      simpa only [Bool.or_eq_true,decide_eq_true_eq] using condition
    obtain ⟨out,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    exact Prep.forIn_inv (edgeStep indegree bi) source[bi]!.zipIdx.toList
      (fun _ nodes => Owners f source nodes) (fun _ pair _ _ inside valid step =>
        edge_valid valid owner step) (edge_not_done indegree bi) _ _ (push_original valid bi) loop
  · cases run
    exact push_original valid bi
private theorem node_not_done (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source indegree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨out,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]
private theorem order_owners {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order) :
    ∃ source,stockSourceTable f = .ok source ∧ Owners f source order.nodes := by
  unfold blockOrder at run
  simp only [bind,Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    have computed : stockSourceTable f = .ok source := by
      unfold stockSourceTable
      apply Eq.trans ?_ sourceRun
      congr 2
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
        have valid : Owners f source nodes := Prep.forIn_inv (nodeStep f source indegree) _
          (fun _ nodes => Owners f source nodes)
          (fun _ _ _ _ _ valid step => node_valid valid step)
          (node_not_done f source indegree) _ _ (by intro pred index target member; simp at member) loop
        split at run
        · cases run
        · cases run
          exact ⟨source,computed,valid⟩

/-- Single-successor source jumps never own synthetic critical nodes, even when
other source blocks have forced or critical edges. -/
theorem jump_no_edge {f : Clif.Function} {order : Order} (ordered : blockOrder f = .ok order)
    {bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (found : f.blocks[bi]? = some b) (jump : b.term = .jump bc) :
    ∀ index target,Node.edge bi index target ∉ order.nodes.toList := by
  obtain ⟨source,computed,owners⟩ := order_owners ordered
  intro index target member
  have size := ForwardSource.source_row_size computed found
  have block : f.blocks[bi]! = b := by simp only [getElem!_def,found,Option.getD_some]
  have owner := owners bi index target member
  simp only [block,jump,forceTerm,Bool.false_eq_true,false_or] at owner
  simp only [jump,destinations,List.length_cons,List.length_nil] at size
  omega

/-- Actual source jumps select their original target directly. Critical nodes
belonging to other blocks do not change this fact. -/
theorem jump_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (term : b.term = .jump bc) :
    ∃ target targetLabel,blockIdx? f bc.block = some target ∧ target ≠ 0 ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) := by
  obtain ⟨target,targetLabel,found,nonentry,successors,node⟩ :=
    stock_lower_jump_nonentry_successor run scope tag block term
  refine ⟨target,targetLabel,found,nonentry,successors,?_⟩
  rcases node with original | synthetic
  · exact original
  · exact False.elim (jump_no_edge (stock_lower_order run) block term 0 target
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? synthetic)))

end Backend.Stock.Proof.CriticalOwners

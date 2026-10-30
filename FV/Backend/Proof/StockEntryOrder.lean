import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def edgeStep (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes : Array Node) :
    Except String (ForInStep (Array Node)) :=
  if indegree[pair.1]! > 1 then pure (.yield (nodes.push (.edge bi pair.2 pair.1)))
  else pure (.yield nodes)

private def force (term : Clif.Terminator) : Bool :=
  match term with | .brTable .. | .tryCall .. | .tryCallIndirect .. => true | _ => false

private def nodeStep (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes : Array Node) : Except String (ForInStep (Array Node)) := do
  let nodes := nodes.push (.original bi)
  if force f.blocks[bi]!.term || source[bi]!.size > 1 then
    let next ← forIn source[bi]!.zipIdx nodes (edgeStep indegree bi)
    pure (.yield next)
  else pure (.yield nodes)

private theorem head_push {nodes : Array Node} {head : Node} (hasHead : nodes[0]? = some head) (node : Node) :
    (nodes.push node)[0]? = some head := by
  have bound := (Array.getElem?_eq_some_iff.mp hasHead).1
  simpa only [Array.getElem?_push,show 0 ≠ nodes.size by omega,ite_false] using hasHead

private theorem edge_head (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat)
    {nodes next : Array Node} {head : Node} (hasHead : nodes[0]? = some head)
    (run : edgeStep indegree bi pair nodes = .ok (.yield next)) : next[0]? = some head := by
  unfold edgeStep at run
  split at run <;> cases run
  · exact head_push hasHead _
  · exact hasHead

private theorem edge_noBreak (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat)
    (nodes next : Array Node) : edgeStep indegree bi pair nodes ≠ .ok (.done next) := by
  unfold edgeStep
  split <;> simp [pure,Except.pure]

private theorem edges_head (indegree : Array Nat) (bi : Nat) (xs : Array (Nat × Nat))
    {nodes next : Array Node} {head : Node} (hasHead : nodes[0]? = some head)
    (run : forIn xs nodes (edgeStep indegree bi) = .ok next) : next[0]? = some head := by
  rw [← Array.forIn_toList] at run
  exact Prep.forIn_inv (edgeStep indegree bi) xs.toList (fun _ nodes => nodes[0]? = some head)
    (fun _ x _ _ _ hi hs => edge_head indegree bi x hi hs) (edge_noBreak indegree bi)
    nodes next hasHead run

private theorem node_head (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) {nodes next : Array Node} {head : Node} (hasHead : (nodes.push (.original bi))[0]? = some head)
    (run : nodeStep f source indegree bi nodes = .ok (.yield next)) : next[0]? = some head := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · obtain ⟨after,loop,run⟩ := Except.bind_ok run
    cases run
    exact edges_head indegree bi _ hasHead loop
  · cases run
    exact hasHead

private theorem node_noBreak (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source indegree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨_,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]

private theorem nodes_head (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (xs : List Nat) {nodes next : Array Node} {head : Node} (hasHead : nodes[0]? = some head)
    (run : forIn xs nodes (nodeStep f source indegree) = .ok next) : next[0]? = some head :=
  Prep.forIn_inv (nodeStep f source indegree) xs (fun _ nodes => nodes[0]? = some head)
    (fun _ bi _ _ _ hi hs => node_head f source indegree bi (head_push hi _) hs)
    (node_noBreak f source indegree) nodes next hasHead run

/-- Actual Stock order puts original source block0 at lowered label0, before
any critical-edge nodes. The original source's nonemptiness is sufficient. -/
theorem stock_blockOrder_entry {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks ≠ []) :
    order.nodes[0]? = some (.original 0) := by
  unfold blockOrder at run
  simp only [bind,Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    have computed : stockSourceTable f = .ok source := by
      unfold stockSourceTable
      apply Eq.trans ?_ sourceRun
      congr 2
    obtain ⟨size,bounds⟩ := stock_sourceTable_bounds computed
    have nonzero : source.size ≠ 0 := by rw [size]; exact fun h => nonempty (List.length_eq_zero_iff.mp h)
    have first := (Prep.rpo_spec bounds nonzero).2.2.1
    have listHead : (rpo source).toList = 0 :: (rpo source).toList.tail := by
      cases list : (rpo source).toList with
      | nil => rw [← Array.getElem?_toList,list] at first; cases first
      | cons x xs =>
        rw [← Array.getElem?_toList,list] at first
        simp only [List.getElem?_cons_zero,Option.some.injEq] at first
        simp [first]
    split at run
    · cases run
    · rename_i indegree degreeRun
      split at run
      · cases run
      · rename_i nodes nodesRun
        have loop : forIn (rpo source) #[] (nodeStep f source indegree) = .ok nodes := by
          apply Eq.trans ?_ nodesRun
          congr 2
        rw [← Array.forIn_toList,listHead,List.forIn_cons] at loop
        cases initial : nodeStep f source indegree 0 #[] with
        | error err => simp only [initial,bind,Except.bind] at loop; cases loop
        | ok step =>
          cases step with
          | done _ => exact False.elim (node_noBreak f source indegree 0 _ _ initial)
          | yield next =>
            simp only [initial,bind,Except.bind] at loop
            have head : next[0]? = some (.original 0) :=
              node_head f source indegree 0 (nodes := #[]) (by rfl) initial
            have retained := nodes_head f source indegree _ head loop
            split at run
            · cases run
            · simp only [pure,Except.pure] at run
              cases run
              exact retained

private theorem mapM_lookup {α β : Type} {xs : Array α} {ys : Array β}
    {step : α → Except String β} (run : xs.mapM step = .ok ys)
    {i : Nat} {y : β} (lookup : ys[i]? = some y) :
    ∃ x,xs[i]? = some x ∧ step x = .ok y := by
  obtain ⟨size,calls⟩ := Prep.amapM_ok run
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp lookup
  have hx : i < xs.size := by omega
  obtain ⟨z,call,atZ⟩ := calls i xs[i] (Array.getElem?_eq_getElem hx)
  rw [lookup] at atZ
  cases atZ
  exact ⟨xs[i],Array.getElem?_eq_getElem hx,call⟩

private theorem destination_ids (term : Clif.Terminator) :
    (destinations term).map Prod.fst = succIds term := by
  cases term <;> simp [destinations,succIds,dests,List.map_map,Function.comp_def]

/-- Original LowerScope forbids source entry predecessors in the exact actual
Stock source-successor table, for every branch and TryCall destination form. -/
theorem stock_sourceTable_nonentry {f : Clif.Function} {source : Array (Array Nat)}
    (run : stockSourceTable f = .ok source) (scope : LowerScope f) :
    ∀ (b : Nat) (row : Array Nat),source[b]? = some row → 0 ∉ row.toList := by
  intro b row atRow member
  obtain ⟨block,found,blockRun⟩ := mapM_lookup run atRow
  have sourceMember : block ∈ f.blocks := by
    simpa using Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  obtain ⟨j,atZero⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨destination,atDest,destRun⟩ := mapM_lookup blockRun atZero
  have destinationMember : destination.1 ∈ succIds block.term := by
    rw [← destination_ids]
    apply List.mem_map.mpr
    exact ⟨destination,by simpa using Array.mem_toList_iff.mpr (Array.mem_of_getElem? atDest),rfl⟩
  have absent := scope.noEntryPred block sourceMember destination.1 destinationMember
  cases target : f.blocks.findIdx? (·.id == destination.1) with
  | none => simp only [target,throw,throwThe,MonadExceptOf.throw] at destRun; cases destRun
  | some index =>
    simp only [target,pure,Except.pure,Except.ok.injEq] at destRun
    subst index
    exact absent target

private def NoEntryEdges (nodes : Array Node) : Prop :=
  ∀ pred index,Node.edge pred index 0 ∉ nodes.toList

private theorem noEntry_push_original {nodes : Array Node} (h : NoEntryEdges nodes) (bi : Nat) :
    NoEntryEdges (nodes.push (.original bi)) := by
  intro pred index member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | impossible
  · exact h pred index old
  · cases impossible

private theorem noEntry_push_edge {nodes : Array Node} (h : NoEntryEdges nodes)
    (bi k target : Nat) (nonzero : target ≠ 0) : NoEntryEdges (nodes.push (.edge bi k target)) := by
  intro pred index member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | equal
  · exact h pred index old
  · have zero := (Node.edge.inj equal).2.2
    exact nonzero zero.symm

private theorem edge_nonentry (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat)
    {nodes next : Array Node} (h : NoEntryEdges nodes) (nonzero : pair.1 ≠ 0)
    (run : edgeStep indegree bi pair nodes = .ok (.yield next)) : NoEntryEdges next := by
  unfold edgeStep at run
  split at run <;> cases run
  · exact noEntry_push_edge h bi pair.2 pair.1 nonzero
  · exact h

private theorem node_nonentry (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (sourceNoEntry : ∀ bi : Nat,0 ∉ source[bi]!.toList) (bi : Nat) {nodes next : Array Node}
    (h : NoEntryEdges nodes) (run : nodeStep f source indegree bi nodes = .ok (.yield next)) :
    NoEntryEdges next := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · obtain ⟨after,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    exact Prep.forIn_inv (edgeStep indegree bi) source[bi]!.zipIdx.toList
      (fun _ state => NoEntryEdges state) (fun _ x _ _ hx hi hs => by
        have found := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp (List.mem_of_getElem? hx))
        have member : x.1 ∈ source[bi]!.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
        have nonzero : x.1 ≠ 0 := by intro zero; rw [zero] at member; exact sourceNoEntry bi member
        exact edge_nonentry indegree bi x hi nonzero hs)
      (edge_noBreak indegree bi) _ _ (noEntry_push_original h bi) loop
  · cases run
    exact noEntry_push_original h bi

/-- No actual synthetic node in Stock's computed order targets source entry0.
This follows from the original source scope and actual edge insertion loops. -/
theorem stock_blockOrder_edges_nonentry {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (scope : LowerScope f) :
    ∀ pred index,Node.edge pred index 0 ∉ order.nodes.toList := by
  unfold blockOrder at run
  simp only [bind,Except.bind] at run
  split at run
  · cases run
  · rename_i source sourceRun
    have computed : stockSourceTable f = .ok source := by
      unfold stockSourceTable
      apply Eq.trans ?_ sourceRun
      congr 2
    have sourceNoEntry : ∀ bi : Nat,0 ∉ source[bi]!.toList := by
      intro bi
      cases row : source[bi]? with
      | none =>
        simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,row,Option.getD_none]
        change 0 ∉ ([] : List Nat)
        simp
      | some ss =>
        simpa only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,row,Option.getD_some] using
          stock_sourceTable_nonentry computed scope bi ss row
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
        have retained : NoEntryEdges nodes := Prep.forIn_inv (nodeStep f source indegree) _
          (fun _ state => NoEntryEdges state)
          (fun _ bi _ _ _ hi hs => node_nonentry f source indegree sourceNoEntry bi hi hs)
          (node_noBreak f source indegree) _ _ (by intro pred index member; simp at member) loop
        split at run
        · cases run
        · simp only [pure,Except.pure] at run
          cases run
          exact retained

end Backend.Stock.Proof

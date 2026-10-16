import FV.Backend.Proof.StockCriticalSplit

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def owner : Node → Nat
  | .original bi | .edge bi .. => bi
private def selected (degree : Array Nat) (bi : Nat) (xs : List (Nat × Nat)) : List Node :=
  (xs.filter fun pair => decide (1 < degree[pair.1]!)).map fun pair => .edge bi pair.2 pair.1
private def chunk (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat) (bi : Nat) : List Node :=
  .original bi :: if forceCritical f.blocks[bi]!.term || source[bi]!.size > 1 then
    selected degree bi source[bi]!.toList.zipIdx else []
private def edgeStep (degree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes : Array Node) :
    Except String (ForInStep (Array Node)) :=
  if degree[pair.1]! > 1 then pure (.yield (nodes.push (.edge bi pair.2 pair.1))) else pure (.yield nodes)
private def nodeStep (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat)
    (bi : Nat) (nodes : Array Node) : Except String (ForInStep (Array Node)) := do
  let nodes := nodes.push (.original bi)
  if forceCritical f.blocks[bi]!.term || source[bi]!.size > 1 then
    let next ← forIn source[bi]!.zipIdx nodes (edgeStep degree bi)
    pure (.yield next)
  else pure (.yield nodes)
private theorem edge_loop_list (degree : Array Nat) (bi : Nat) :
    ∀ (xs : List (Nat × Nat)) (nodes next : Array Node),forIn xs nodes (edgeStep degree bi) = .ok next →
      next.toList = nodes.toList ++ selected degree bi xs := by
  intro xs
  induction xs with
  | nil =>
    intro nodes next run
    simp only [List.forIn_nil,pure,Except.pure,Except.ok.injEq] at run
    subst next
    simp [selected]
  | cons pair xs ih =>
    intro nodes next run
    rw [List.forIn_cons] at run
    unfold edgeStep at run
    split at run
    · rename_i shared
      simp only [pure,Except.pure,bind,Except.bind] at run
      rw [ih _ _ run]
      simp [selected,shared,Array.toList_push,List.append_assoc]
    · rename_i notShared
      simp only [pure,Except.pure,bind,Except.bind] at run
      rw [ih _ _ run]
      simp [selected,notShared]
private theorem node_list {f : Clif.Function} {source : Array (Array Nat)} {degree : Array Nat}
    {bi : Nat} {nodes next : Array Node} (run : nodeStep f source degree bi nodes = .ok (.yield next)) :
    next.toList = nodes.toList ++ chunk f source degree bi := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · rename_i forced
    obtain ⟨out,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    rw [edge_loop_list degree bi _ _ _ loop]
    unfold chunk
    rw [if_pos forced]
    simp only [Array.toList_push,Array.toList_zipIdx,List.append_assoc,List.singleton_append]
  · rename_i notForced
    cases run
    unfold chunk
    rw [if_neg notForced]
    simp only [Array.toList_push,List.append_nil,List.singleton_append]
private theorem node_not_done (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source degree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨out,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]
private theorem nodes_list (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat) :
    ∀ (indices : List Nat) (nodes next : Array Node),forIn indices nodes (nodeStep f source degree) = .ok next →
      next.toList = nodes.toList ++ indices.flatMap (chunk f source degree) := by
  intro indices
  induction indices with
  | nil =>
    intro nodes next run
    simp only [List.forIn_nil,pure,Except.pure,Except.ok.injEq] at run
    subst next; simp
  | cons bi indices ih =>
    intro nodes next run
    rw [List.forIn_cons] at run
    obtain ⟨step,call,run⟩ := Except.bind_ok run
    cases step with
    | done stopped => exact False.elim (node_not_done f source degree bi nodes stopped call)
    | yield mid => rw [ih _ _ run,node_list call]; simp [List.append_assoc]

private theorem chunk_owner (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat) (bi : Nat) :
    ∀ node ∈ chunk f source degree bi,owner node = bi := by
  intro node member
  unfold chunk at member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · split at member
    · obtain ⟨pair,_,rfl⟩ := List.mem_map.mp member
      rfl
    · cases member
private theorem chunk_nodup (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat) (bi : Nat) :
    (chunk f source degree bi).Nodup := by
  unfold chunk
  rw [List.nodup_cons]
  split
  · constructor
    · intro member
      obtain ⟨pair,_,same⟩ := List.mem_map.mp member
      cases same
    · have indices : (source[bi]!.toList.zipIdx.map Prod.snd).Nodup := by
        rw [List.zipIdx_map_snd]
        exact List.nodup_range' _
      have filtered : (((source[bi]!.toList.zipIdx).filter fun pair => decide (1 < degree[pair.1]!)).map Prod.snd).Nodup :=
        indices.sublist (List.filter_sublist.map _)
      unfold selected
      rw [List.Nodup,List.pairwise_map] at filtered ⊢
      exact filtered.imp_of_mem fun _ _ different same => different (by injection same)
  · exact ⟨by simp,List.nodup_nil⟩
private theorem chunks_nodup (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat) :
    ∀ indices : List Nat,indices.Nodup → (indices.flatMap (chunk f source degree)).Nodup := by
  intro indices nd
  induction indices with
  | nil => exact List.nodup_nil
  | cons bi indices ih =>
    rw [List.nodup_cons] at nd
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨chunk_nodup f source degree bi,ih nd.2,?_⟩
    intro x hx y hy same
    obtain ⟨bj,member,hy⟩ := List.mem_flatMap.mp hy
    have first := chunk_owner f source degree bi x hx
    have second := chunk_owner f source degree bj y hy
    have eq : bi = bj := first.symm.trans ((congrArg owner same).trans second)
    exact nd.1 (eq ▸ member)

/-- Every actual Stock order node is unique, including all inserted critical
nodes. Selected successor indices distinguish repeated source destinations;
source RPO uniqueness separates nodes owned by different source blocks. -/
theorem stock_blockOrder_nodes_nodup {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0) : order.nodes.toList.Nodup := by
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
    · rename_i degree degreeRun
      split at run
      · cases run
      · rename_i nodes nodesRun
        have loop : forIn (rpo source) #[] (nodeStep f source degree) = .ok nodes := by
          apply Eq.trans ?_ nodesRun
          congr 2
        rw [← Array.forIn_toList] at loop
        have projection := nodes_list f source degree _ _ _ loop
        simp only [Array.toList_empty,List.nil_append] at projection
        have nd := chunks_nodup f source degree _ (stock_sourceTable_rpo computed nonempty).1
        split at run
        · cases run
        · cases run
          rw [projection]
          exact nd

/-- Any two actual Stock node lookups with the same complete node identity
have the same index, for original as well as critical nodes. -/
theorem stock_blockOrder_node_unique {f : Clif.Function} {order : Order}
    (run : blockOrder f = .ok order) (nonempty : f.blocks.length ≠ 0)
    {i j : Nat} {node : Node} (first : order.nodes[i]? = some node) (second : order.nodes[j]? = some node) : i = j := by
  have nd := stock_blockOrder_nodes_nodup run nonempty
  obtain ⟨ibound,ieq⟩ := Array.getElem?_eq_some_iff.mp first
  obtain ⟨jbound,jeq⟩ := Array.getElem?_eq_some_iff.mp second
  rcases Nat.lt_trichotomy i j with before | same | after
  · have different := List.Pairwise.rel_getElem_of_lt (by simpa using ibound) (by simpa using jbound) nd before
    exact False.elim (different (by simpa only [Array.getElem_toList,ieq,jeq]))
  · exact same
  · have different := List.Pairwise.rel_getElem_of_lt (by simpa using jbound) (by simpa using ibound) nd after
    exact False.elim (different (by simpa only [Array.getElem_toList,ieq,jeq]))

/-- Successful nonempty Stock lowering has no duplicate original or critical
nodes; this applies under the unchanged original scope condition. -/
theorem stock_lower_nodes_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) : result.order.nodes.toList.Nodup :=
  stock_blockOrder_nodes_nodup (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))

end Backend.Stock.Proof

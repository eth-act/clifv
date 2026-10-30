import FV.Backend.Proof.StockEdgeCode

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem idx_go {α β : Type} (f : Nat → α → Except String β) :
    ∀ (xs : List α) (acc : Array β) (ys : List β),List.mapIdxM.go f xs acc = .ok ys →
    ys.length = acc.size+xs.length ∧
    (∀ i,i < acc.size → ys[i]? = acc[i]?) ∧
    ∀ (j : Nat) (x : α),xs[j]? = some x → ∃ y,f (acc.size+j) x = .ok y ∧ ys[acc.size+j]? = some y := by
  intro xs
  induction xs with
  | nil =>
    intro acc ys run
    simp only [List.mapIdxM.go,pure,Except.pure,Except.ok.injEq] at run
    subst ys
    exact ⟨by simp,fun _ _ => by simp,fun j x atX => by simp at atX⟩
  | cons x xs ih =>
    intro acc ys run
    simp only [List.mapIdxM.go] at run
    obtain ⟨y,first,rest⟩ := Except.bind_ok run
    obtain ⟨size,kept,calls⟩ := ih (acc.push y) ys rest
    refine ⟨by simp only [Array.size_push,List.length_cons] at size ⊢; omega,?_,?_⟩
    · intro i bound
      rw [kept i (by simp only [Array.size_push]; omega),Array.getElem?_push]
      simp only [show i ≠ acc.size by omega,ite_false]
    · intro j z atZ
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at atZ
        subst z
        refine ⟨y,by simpa using first,?_⟩
        simpa using kept acc.size (by simp)
      | succ j =>
        obtain ⟨z',call,lookup⟩ := calls j z (by simpa using atZ)
        exact ⟨z',by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using call,
          by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lookup⟩

private theorem idx_lookup {α β : Type} {f : Nat → α → Except String β} {xs : Array α} {ys : Array β}
    (run : xs.mapIdxM f = .ok ys) {j : Nat} {y : β} (atY : ys[j]? = some y) :
    ∃ x,xs[j]? = some x ∧ f j x = .ok y := by
  have normal : xs.mapIdxM f = List.toArray <$> xs.toList.mapIdxM f := by
    simpa using (List.mapIdxM_toArray (l := xs.toList) (f := f))
  rw [normal] at run
  cases mapped : xs.toList.mapIdxM f with
  | error err => simp only [mapped,Functor.map,Except.map] at run; cases run
  | ok values =>
    simp only [mapped,Functor.map,Except.map,Except.ok.injEq] at run
    subst ys
    obtain ⟨count,_,calls⟩ := idx_go f xs.toList #[] values mapped
    have bound : j < xs.size := by
      have h := (Array.getElem?_eq_some_iff.mp atY).1
      simp only [List.size_toArray] at h
      simp only [Array.size_empty,Nat.zero_add,Array.length_toList] at count
      omega
    obtain ⟨v,call,atV⟩ := calls j xs[j] (by simp [bound])
    simp only [Array.size_empty,Nat.zero_add] at call atV
    have atY' : values[j]? = some y := by simpa only [List.getElem?_toArray] using atY
    rw [atY'] at atV
    cases atV
    exact ⟨xs[j],Array.getElem?_eq_getElem bound,call⟩

private def graphLabel (nodes : Array Node) (node : Node) : Except String Nat :=
  match nodes.findIdx? (· == node) with
  | some i => pure i
  | none => throw "missing lowered block"
private def successors (source : Array (Array Nat)) (nodes : Array Node) : Node → Except String (Array Nat)
  | .edge _ _ s => return #[← graphLabel nodes (.original s)]
  | .original bi => source[bi]!.mapIdxM fun k s =>
    if nodes.contains (.edge bi k s) then graphLabel nodes (.edge bi k s) else graphLabel nodes (.original s)
private theorem graph_run {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order) :
    ∃ source,stockSourceTable f = .ok source ∧ order.nodes.mapM (successors source order.nodes) = .ok order.successors := by
  unfold blockOrder at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,by assumption,by assumption⟩
private theorem label_lookup {nodes : Array Node} {node : Node} {label : Nat}
    (run : graphLabel nodes node = .ok label) : nodes[label]? = some node := by
  unfold graphLabel at run
  cases found : nodes.findIdx? (· == node) with
  | none => simp [found] at run
  | some i =>
    simp only [found,pure,Except.pure,Except.ok.injEq] at run
    subst label
    obtain ⟨bound,same,_⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have equal : nodes[i] = node := by simpa using same
    simp only [Array.getElem?_eq_getElem bound,equal]

private theorem source_selected {f : Clif.Function} {source : Array (Array Nat)}
    (run : stockSourceTable f = .ok source) {bi j target : Nat} {ss : Array Nat}
    (row : source[bi]? = some ss) (edge : ss[j]? = some target) :
    ∃ (b : Clif.Block) (id : Nat) (args : List Clif.TryArg),f.blocks[bi]? = some b ∧
      (destinations b.term)[j]? = some (id,args) ∧ f.blocks.findIdx? (·.id == id) = some target := by
  unfold stockSourceTable at run
  obtain ⟨size,calls⟩ := array_mapM_ok run
  have bound : bi < f.blocks.length := by
    have h := (Array.getElem?_eq_some_iff.mp row).1
    simpa only [size,List.size_toArray] using h
  obtain ⟨out,mapped,atOut⟩ := calls bi f.blocks[bi] (by simp [bound])
  rw [row] at atOut
  cases atOut
  obtain ⟨count,items⟩ := array_mapM_ok mapped
  have jBound : j < (destinations f.blocks[bi].term).length := by
    have h := (Array.getElem?_eq_some_iff.mp edge).1
    simpa only [count,List.size_toArray] using h
  obtain ⟨pair,atDest⟩ : ∃ pair,(destinations f.blocks[bi].term)[j]? = some pair :=
    ⟨_,List.getElem?_eq_getElem jBound⟩
  obtain ⟨id,args⟩ := pair
  obtain ⟨out,call,atOut⟩ := items j (id,args) (by simpa only [List.getElem?_toArray] using atDest)
  rw [edge] at atOut
  cases atOut
  cases found : f.blocks.findIdx? (·.id == id) with
  | none => simp [found] at call
  | some n =>
    simp only [found,pure,Except.pure,Except.ok.injEq] at call
    subst n
    exact ⟨f.blocks[bi],id,args,by simp [bound],atDest,found⟩

/-- Every actual indexed successor of an original Stock node selects the same
original source destination. The returned target is either its original node
or precisely that successor's synthetic node, including duplicate destinations
and every ordinary/TryCall form. No CFG/branch-format certificate is supplied. -/
theorem stock_lower_indexed_successor_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi j targetLabel : Nat} {ss : Array Nat}
    (node : result.order.nodes[label]? = some (.original bi))
    (row : result.order.successors[label]? = some ss) (edge : ss[j]? = some targetLabel) :
    ∃ (b : Clif.Block) (id : Nat) (args : List Clif.TryArg) (target : Nat),
      f.blocks[bi]? = some b ∧ (destinations b.term)[j]? = some (id,args) ∧
      f.blocks.findIdx? (·.id == id) = some target ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge bi j target)) := by
  obtain ⟨source,computed,graph⟩ := graph_run (stock_lower_order run)
  obtain ⟨out,mapped,atOut⟩ := (array_mapM_ok graph).2 label _ node
  rw [row] at atOut
  cases atOut
  unfold successors at mapped
  obtain ⟨target,atTarget,call⟩ := idx_lookup mapped edge
  have sourceRow : source[bi]? = some source[bi]! := by
    cases found : source[bi]? with
    | none => simp only [getElem!_def,found] at atTarget; cases atTarget
    | some ss => simpa only [getElem!_def,found] using found
  obtain ⟨b,id,args,sourceBlock,dest,found⟩ := source_selected computed sourceRow atTarget
  refine ⟨b,id,args,target,sourceBlock,dest,found,?_⟩
  split at call
  · exact Or.inr (label_lookup call)
  · exact Or.inl (label_lookup call)

private def NodeEdgesValid (source : Array (Array Nat)) (nodes : Array Node) : Prop :=
  ∀ pred index target,Node.edge pred index target ∈ nodes.toList → source[pred]![index]? = some target
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
private theorem push_original_valid {source : Array (Array Nat)} {nodes : Array Node}
    (valid : NodeEdgesValid source nodes) (bi : Nat) : NodeEdgesValid source (nodes.push (.original bi)) := by
  intro pred index target member
  simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | same
  · exact valid pred index target old
  · cases same
private theorem edge_valid {source : Array (Array Nat)} {indegree : Array Nat} {bi : Nat}
    {pair : Nat × Nat} {nodes next : Array Node} (valid : NodeEdgesValid source nodes)
    (edge : source[bi]![pair.2]? = some pair.1)
    (run : edgeStep indegree bi pair nodes = .ok (.yield next)) : NodeEdgesValid source next := by
  unfold edgeStep at run
  split at run <;> cases run
  · intro pred index target member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact valid pred index target old
    · cases same; exact edge
  · exact valid
private theorem edge_not_done (indegree : Array Nat) (bi : Nat) (pair : Nat × Nat) (nodes next : Array Node) :
    edgeStep indegree bi pair nodes ≠ .ok (.done next) := by
  unfold edgeStep
  split <;> simp [pure,Except.pure]
private theorem node_valid {f : Clif.Function} {source : Array (Array Nat)} {indegree : Array Nat}
    {bi : Nat} {nodes next : Array Node} (valid : NodeEdgesValid source nodes)
    (run : nodeStep f source indegree bi nodes = .ok (.yield next)) : NodeEdgesValid source next := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · obtain ⟨out,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    exact Prep.forIn_inv (edgeStep indegree bi) source[bi]!.zipIdx.toList
      (fun _ nodes => NodeEdgesValid source nodes) (fun _ pair _ _ inside valid step => by
        have selected := Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp (List.mem_of_getElem? inside))
        exact edge_valid valid selected step)
      (edge_not_done indegree bi) _ _ (push_original_valid valid bi) loop
  · cases run
    exact push_original_valid valid bi
private theorem node_not_done (f : Clif.Function) (source : Array (Array Nat)) (indegree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source indegree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨out,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]
private theorem order_edges_valid {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order) :
    ∃ source,stockSourceTable f = .ok source ∧ NodeEdgesValid source order.nodes := by
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
        have valid : NodeEdgesValid source nodes := Prep.forIn_inv (nodeStep f source indegree) _
          (fun _ nodes => NodeEdgesValid source nodes)
          (fun _ _ _ _ _ valid step => node_valid valid step)
          (node_not_done f source indegree) _ _ (by intro pred index target member; simp at member) loop
        split at run
        · cases run
        · cases run
          exact ⟨source,computed,valid⟩

/-- Every actual critical node records a real source edge at precisely its
predecessor/successor index, including repeated destinations. The source target
lookup agrees with the target index carried by that actual node. -/
theorem stock_lower_critical_source {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label pred index target : Nat}
    (node : result.order.nodes[label]? = some (.edge pred index target)) :
    ∃ (b : Clif.Block) (id : Nat) (args : List Clif.TryArg),f.blocks[pred]? = some b ∧
      (destinations b.term)[index]? = some (id,args) ∧ f.blocks.findIdx? (·.id == id) = some target := by
  obtain ⟨source,computed,valid⟩ := order_edges_valid (stock_lower_order run)
  have edge := valid pred index target (Array.mem_toList_iff.mpr (Array.mem_of_getElem? node))
  have sourceRow : source[pred]? = some source[pred]! := by
    cases found : source[pred]? with
    | none => simp only [getElem!_def,found] at edge; cases edge
    | some ss => simpa only [getElem!_def,found] using found
  exact source_selected computed sourceRow edge

end Backend.Stock.Proof

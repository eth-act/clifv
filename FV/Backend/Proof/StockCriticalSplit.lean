import FV.Backend.Proof.StockGraphEdges

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The actual source indegree computation counts duplicate and unreachable
source edges before reachable Stock nodes are selected. -/
def sourceIndegree (source : Array (Array Nat)) (size : Nat) : Except String (Array Nat) := do
  let mut degree := Array.replicate size 0
  for ss in source do
    for s in ss do degree := degree.modify s (· + 1)
  pure degree

def forceCritical : Clif.Terminator → Bool
  | .brTable .. | .tryCall .. | .tryCallIndirect .. => true
  | _ => false

/-- Every visited original node has all required selected critical nodes,
including forced one-successor TryCall/brTable edges. This is a construction
property, complementary to critical-node provenance. -/
def CriticalSplitComplete (f : Clif.Function) (source : Array (Array Nat))
    (degree : Array Nat) (nodes : Array Node) : Prop :=
  ∀ bi,Node.original bi ∈ nodes.toList → ∀ k target,source[bi]![k]? = some target →
    (forceCritical f.blocks[bi]!.term || decide (1 < source[bi]!.size)) = true →
    1 < degree[target]! → Node.edge bi k target ∈ nodes.toList

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

private theorem edge_loop (degree : Array Nat) (bi : Nat) :
    ∀ (xs : List (Nat × Nat)) (nodes next : Array Node),forIn xs nodes (edgeStep degree bi) = .ok next →
      (∀ node,node ∈ nodes.toList → node ∈ next.toList) ∧
      (∀ source,Node.original source ∈ next.toList → Node.original source ∈ nodes.toList) ∧
      ∀ pair ∈ xs,1 < degree[pair.1]! → Node.edge bi pair.2 pair.1 ∈ next.toList := by
  intro xs
  induction xs with
  | nil =>
    intro nodes next run
    simp only [List.forIn_nil,pure,Except.pure,Except.ok.injEq] at run
    subst next
    exact ⟨fun _ h => h,fun _ h => h,fun _ h => by cases h⟩
  | cons pair xs ih =>
    intro nodes next run
    rw [List.forIn_cons] at run
    unfold edgeStep at run
    split at run
    · rename_i shared
      simp only [pure,Except.pure,bind,Except.bind] at run
      obtain ⟨kept,original,inserted⟩ := ih _ _ run
      refine ⟨fun node h => kept node (by simp only [Array.toList_push,List.mem_append,List.mem_singleton]; exact .inl h),?_,?_⟩
      · intro source member
        have before := original source member
        simp only [Array.toList_push,List.mem_append,List.mem_singleton] at before
        rcases before with old | same
        · exact old
        · cases same
      · intro p member high
        rcases List.mem_cons.mp member with rfl | old
        · exact kept _ (by simp)
        · exact inserted p old high
    · rename_i notShared
      simp only [pure,Except.pure,bind,Except.bind] at run
      obtain ⟨kept,original,inserted⟩ := ih _ _ run
      refine ⟨kept,original,?_⟩
      intro p member high
      rcases List.mem_cons.mp member with rfl | old
      · exact False.elim (notShared high)
      · exact inserted p old high

private theorem node_complete {f : Clif.Function} {source : Array (Array Nat)} {degree : Array Nat}
    {bi : Nat} {nodes next : Array Node} (complete : CriticalSplitComplete f source degree nodes)
    (run : nodeStep f source degree bi nodes = .ok (.yield next)) : CriticalSplitComplete f source degree next := by
  unfold nodeStep at run
  dsimp only at run
  split at run
  · rename_i forced
    obtain ⟨out,loop,run⟩ := Except.bind_ok run
    cases run
    rw [← Array.forIn_toList] at loop
    obtain ⟨kept,original,inserted⟩ := edge_loop degree bi _ _ _ loop
    intro sourceBi member k target selected need high
    have old := original sourceBi member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton,Node.original.injEq] at old
    rcases old with old | rfl
    · exact kept _ (by simp only [Array.toList_push,List.mem_append,List.mem_singleton]; exact .inl (complete sourceBi old k target selected need high))
    · apply inserted (target,k) _ high
      exact Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr selected)
  · rename_i notForced
    cases run
    intro sourceBi member k target selected need high
    simp only [Array.toList_push,List.mem_append,List.mem_singleton,Node.original.injEq] at member
    rcases member with old | rfl
    · simp only [Array.toList_push,List.mem_append,List.mem_singleton]
      exact .inl (complete sourceBi old k target selected need high)
    · exact False.elim (notForced (by simpa only [Bool.or_eq_true,decide_eq_true_eq] using need))

private theorem node_not_done (f : Clif.Function) (source : Array (Array Nat)) (degree : Array Nat)
    (bi : Nat) (nodes next : Array Node) : nodeStep f source degree bi nodes ≠ .ok (.done next) := by
  unfold nodeStep
  dsimp only
  split
  · intro run
    obtain ⟨out,_,run⟩ := Except.bind_ok run
    cases run
  · simp [pure,Except.pure]

/-- Actual Stock node construction inserts every required critical node. The
source table and indegrees are recovered from the executable construction;
no graph completeness certificate is supplied by the caller. -/
theorem stock_order_critical_split_complete {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order) :
    ∃ source degree,stockSourceTable f = .ok source ∧ sourceIndegree source f.blocks.length = .ok degree ∧
      CriticalSplitComplete f source degree order.nodes := by
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
      have counted : sourceIndegree source f.blocks.length = .ok degree := by
        unfold sourceIndegree
        have counted := congrArg (fun x : Except String (Array Nat) => x >>= fun y => pure y) degreeRun
        simpa only [bind,Except.bind,pure,Except.pure] using counted
      split at run
      · cases run
      · rename_i nodes nodesRun
        have loop : forIn (rpo source) #[] (nodeStep f source degree) = .ok nodes := by
          apply Eq.trans ?_ nodesRun
          congr 2
        rw [← Array.forIn_toList] at loop
        have complete : CriticalSplitComplete f source degree nodes := Prep.forIn_inv (nodeStep f source degree) _
          (fun _ nodes => CriticalSplitComplete f source degree nodes)
          (fun _ _ _ _ _ complete step => node_complete complete step)
          (node_not_done f source degree) _ _ (by intro bi member; simp at member) loop
        split at run
        · cases run
        · cases run
          exact ⟨source,degree,computed,counted,complete⟩

/-- Complete successful Stock lowering inherits the actual critical-node
insertion guarantee, preserving forced one-successor edges. -/
theorem stock_lower_critical_split_complete {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ source degree,stockSourceTable f = .ok source ∧ sourceIndegree source f.blocks.length = .ok degree ∧
      CriticalSplitComplete f source degree result.order.nodes :=
  stock_order_critical_split_complete (stock_lower_order run)

end Backend.Stock.Proof

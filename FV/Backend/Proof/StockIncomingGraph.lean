import FV.Backend.Proof.StockNodeUnique
import FV.Backend.Proof.StockGraphBounds

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

private theorem mapM_lookup {α β : Type} {xs : Array α} {ys : Array β}
    {step : α → Except String β} (run : xs.mapM step = .ok ys) {i : Nat} {y : β} (lookup : ys[i]? = some y) :
    ∃ x,xs[i]? = some x ∧ step x = .ok y := by
  obtain ⟨size,calls⟩ := Prep.amapM_ok run
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp lookup
  have hx : i < xs.size := by omega
  obtain ⟨z,call,atZ⟩ := calls i xs[i] (Array.getElem?_eq_getElem hx)
  rw [lookup] at atZ
  cases atZ
  exact ⟨xs[i],Array.getElem?_eq_getElem hx,call⟩
private theorem source_forward {f : Clif.Function} {source : Array (Array Nat)}
    (computed : stockSourceTable f = .ok source) {bi k target id : Nat} {b : Clif.Block} {args : List Clif.TryArg}
    (block : f.blocks[bi]? = some b) (selected : (destinations b.term)[k]? = some (id,args))
    (found : f.blocks.findIdx? (·.id == id) = some target) : source[bi]![k]? = some target := by
  unfold stockSourceTable at computed
  obtain ⟨row,mapped,atRow⟩ := (array_mapM_ok computed).2 bi b (by simpa using block)
  obtain ⟨value,call,atValue⟩ := (array_mapM_ok mapped).2 k (id,args) (by simpa only [List.getElem?_toArray] using selected)
  dsimp only at call
  rw [found] at call
  cases call
  rw [show source[bi]! = row from by rw [getElem!_def,atRow]]
  exact atValue

/-- A real incoming indexed edge to an original target either comes directly
from an original node with no selected critical node, or is the sole edge of
that exact selected critical node. Both identify the original source edge. -/
def IncomingOriginalAt (result : Result) (source : Array (Array Nat)) (target b j : Nat) : Prop :=
  (∃ bi,result.order.nodes[b]? = some (.original bi) ∧ source[bi]![j]? = some target ∧
    Node.edge bi j target ∉ result.order.nodes.toList) ∨
  ∃ bi k,result.order.nodes[b]? = some (.edge bi k target) ∧ j = 0 ∧ source[bi]![k]? = some target

def sourceEdgeKey : Node → Nat → Nat × Nat
  | .original bi,j => (bi,j)
  | .edge bi k _,_ => (bi,k)

/-- Every actual incoming edge to any original Stock target has exact indexed
source provenance. Direct routing certifies the selected critical node is
absent, rather than merely permitting an original-or-critical alternative. -/
theorem stock_lower_incoming_original {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ source,stockSourceTable f = .ok source ∧ ∀ targetLabel target,
      result.order.nodes[targetLabel]? = some (.original target) →
      ∀ (b j : Nat) (ss : Array Nat),result.order.successors[b]? = some ss → ss[j]? = some targetLabel →
        IncomingOriginalAt result source target b j := by
  obtain ⟨source,computed,graph⟩ := graph_run (stock_lower_order run)
  refine ⟨source,computed,?_⟩
  intro targetLabel target targetNode b j ss row edge
  obtain ⟨node,atNode,mapped⟩ := mapM_lookup graph row
  cases node with
  | original bi =>
    unfold successors at mapped
    obtain ⟨sourceTarget,selected,call⟩ := idx_lookup mapped edge
    split at call
    · have tag := label_lookup call
      rw [targetNode] at tag
      cases tag
    · rename_i absent
      have tag := label_lookup call
      rw [targetNode] at tag
      have same : sourceTarget = target := (Node.original.inj (Option.some.inj tag)).symm
      subst sourceTarget
      exact .inl ⟨bi,atNode,selected,fun member => absent (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp member))⟩
  | edge bi k sourceTarget =>
    unfold successors at mapped
    obtain ⟨label,call,mapped⟩ := Except.bind_ok mapped
    simp only [pure,Except.pure,Except.ok.injEq] at mapped
    subst ss
    have bound : j < 1 := (Array.getElem?_eq_some_iff.mp edge).1
    have zero : j = 0 := by omega
    subst j
    have sameLabel : label = targetLabel := Option.some.inj edge
    subst label
    have tag := label_lookup call
    rw [targetNode] at tag
    have same : sourceTarget = target := (Node.original.inj (Option.some.inj tag)).symm
    subst sourceTarget
    obtain ⟨block,id,args,sourceBlock,dest,found⟩ := stock_lower_critical_source run atNode
    exact .inr ⟨bi,k,atNode,rfl,source_forward computed sourceBlock dest found⟩

/-- Two actual incoming indexed edges to an original target cannot identify
the same original source edge. Complete node uniqueness handles critical
nodes; direct-route absence excludes mixing direct and split representatives. -/
theorem stock_lower_incoming_source_unique {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel target b₁ j₁ b₂ j₂ : Nat} {ss₁ ss₂ : Array Nat} {node₁ node₂ : Node}
    (targetNode : result.order.nodes[targetLabel]? = some (.original target))
    (firstNode : result.order.nodes[b₁]? = some node₁) (secondNode : result.order.nodes[b₂]? = some node₂)
    (firstRow : result.order.successors[b₁]? = some ss₁) (firstEdge : ss₁[j₁]? = some targetLabel)
    (secondRow : result.order.successors[b₂]? = some ss₂) (secondEdge : ss₂[j₂]? = some targetLabel)
    (sameKey : sourceEdgeKey node₁ j₁ = sourceEdgeKey node₂ j₂) : b₁ = b₂ ∧ j₁ = j₂ := by
  obtain ⟨source,_,incoming⟩ := stock_lower_incoming_original run
  have first := incoming targetLabel target targetNode b₁ j₁ ss₁ firstRow firstEdge
  have second := incoming targetLabel target targetNode b₂ j₂ ss₂ secondRow secondEdge
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  rcases first with ⟨bi₁,tag₁,_,absent₁⟩ | ⟨bi₁,k₁,tag₁,zero₁,_⟩
  all_goals
    have n₁ := Option.some.inj (firstNode.symm.trans tag₁)
    subst node₁
    rcases second with ⟨bi₂,tag₂,_,absent₂⟩ | ⟨bi₂,k₂,tag₂,zero₂,_⟩
    all_goals
      have n₂ := Option.some.inj (secondNode.symm.trans tag₂)
      subst node₂
      simp only [sourceEdgeKey,Prod.mk.injEq] at sameKey
  · obtain ⟨rfl,rfl⟩ := sameKey
    exact ⟨stock_blockOrder_node_unique (stock_lower_order run) nonempty tag₁ tag₂,rfl⟩
  · obtain ⟨rfl,rfl⟩ := sameKey
    exact False.elim (absent₁ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag₂)))
  · obtain ⟨rfl,rfl⟩ := sameKey
    exact False.elim (absent₂ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? tag₁)))
  · obtain ⟨rfl,rfl⟩ := sameKey
    exact ⟨stock_blockOrder_node_unique (stock_lower_order run) nonempty tag₁ tag₂,zero₁.trans zero₂.symm⟩

/-- Every actual incoming edge to a critical node is exactly its selected
original predecessor and successor index. Synthetic nodes only target
original nodes, and different selected indices identify different nodes. -/
theorem stock_lower_incoming_critical {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {targetLabel bi k target b j : Nat} {ss : Array Nat}
    (targetNode : result.order.nodes[targetLabel]? = some (.edge bi k target))
    (row : result.order.successors[b]? = some ss) (edge : ss[j]? = some targetLabel) :
    result.order.nodes[b]? = some (.original bi) ∧ j = k := by
  obtain ⟨source,_,graph⟩ := graph_run (stock_lower_order run)
  obtain ⟨node,atNode,mapped⟩ := mapM_lookup graph row
  cases node with
  | original sourceBi =>
    unfold successors at mapped
    obtain ⟨sourceTarget,selected,call⟩ := idx_lookup mapped edge
    split at call
    · have tag := label_lookup call
      rw [targetNode] at tag
      obtain ⟨sameBi,sameIndex,sameTarget⟩ := Node.edge.inj (Option.some.inj tag)
      exact ⟨by simpa only [← sameBi] using atNode,sameIndex.symm⟩
    · have tag := label_lookup call
      rw [targetNode] at tag
      cases tag
  | edge sourceBi index sourceTarget =>
    unfold successors at mapped
    obtain ⟨label,call,mapped⟩ := Except.bind_ok mapped
    simp only [pure,Except.pure,Except.ok.injEq] at mapped
    subst ss
    have bound : j < 1 := (Array.getElem?_eq_some_iff.mp edge).1
    have zero : j = 0 := by omega
    subst j
    have sameLabel : label = targetLabel := Option.some.inj edge
    subst label
    have tag := label_lookup call
    rw [targetNode] at tag
    cases tag

/-- A critical target has at most one actual incoming indexed edge. This is
independent of source indegree and includes one-successor forced TryCall splits. -/
theorem stock_lower_critical_incoming_unique {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel bi k target b₁ j₁ b₂ j₂ : Nat} {ss₁ ss₂ : Array Nat}
    (targetNode : result.order.nodes[targetLabel]? = some (.edge bi k target))
    (firstRow : result.order.successors[b₁]? = some ss₁) (firstEdge : ss₁[j₁]? = some targetLabel)
    (secondRow : result.order.successors[b₂]? = some ss₂) (secondEdge : ss₂[j₂]? = some targetLabel) :
    b₁ = b₂ ∧ j₁ = j₂ := by
  obtain ⟨first,index₁⟩ := stock_lower_incoming_critical run targetNode firstRow firstEdge
  obtain ⟨second,index₂⟩ := stock_lower_incoming_critical run targetNode secondRow secondEdge
  exact ⟨stock_blockOrder_node_unique (stock_lower_order run)
    (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) first second,index₁.trans index₂.symm⟩

/-- Every actual Stock target with two distinct incoming indexed edges is an
original node. Actual graph bounds supply its node lookup; no target-kind
certificate is required. -/
theorem stock_lower_shared_target_original {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {targetLabel b₁ j₁ b₂ j₂ : Nat} {ss₁ ss₂ : Array Nat}
    (firstRow : result.order.successors[b₁]? = some ss₁) (firstEdge : ss₁[j₁]? = some targetLabel)
    (secondRow : result.order.successors[b₂]? = some ss₂) (secondEdge : ss₂[j₂]? = some targetLabel)
    (distinct : b₁ ≠ b₂ ∨ j₁ ≠ j₂) : ∃ target,result.order.nodes[targetLabel]? = some (.original target) := by
  have bound := (stock_lower_graph_bounds run).2 b₁ ss₁ firstRow targetLabel
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? firstEdge))
  have count : result.code.blocks.size = result.order.nodes.size :=
    (stock_prepare_dimensions run).1.symm.trans (stock_prepare_dimensions run).2.1
  rw [count] at bound
  have node : result.order.nodes[targetLabel]? = some result.order.nodes[targetLabel] := Array.getElem?_eq_getElem bound
  cases tag : result.order.nodes[targetLabel] with
  | original target => exact ⟨target,by simpa only [tag] using node⟩
  | edge bi k target =>
    have critical : result.order.nodes[targetLabel]? = some (.edge bi k target) := by simpa only [tag] using node
    have same := stock_lower_critical_incoming_unique run scope critical firstRow firstEdge secondRow secondEdge
    rcases distinct with different | different
    · exact False.elim (different same.1)
    · exact False.elim (different same.2)

end Backend.Stock.Proof

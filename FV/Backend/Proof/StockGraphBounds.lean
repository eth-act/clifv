import Init.Data.Array.MapIdx
import FV.Backend.Proof.StockPrepareInputs

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

private theorem idx_go_bound {α : Type} {f : Nat → α → Except String Nat} (n : Nat) :
    ∀ (xs : List α) (acc : Array Nat) (out : List Nat),List.mapIdxM.go f xs acc = .ok out →
      (∀ v ∈ acc.toList,v < n) → (∀ j x,x ∈ xs → ∀ v,f j x = .ok v → v < n) →
      ∀ v ∈ out,v < n
  | [], acc, out, run, initial, calls => by
    simp only [List.mapIdxM.go,pure,Except.pure,Except.ok.injEq] at run
    subst out
    exact initial
  | x :: xs, acc, out, run, initial, calls => by
    simp only [List.mapIdxM.go] at run
    obtain ⟨value,first,rest⟩ := Except.bind_ok run
    apply idx_go_bound n xs (acc.push value) out rest
    · intro v member
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
      rcases member with member | rfl
      · exact initial v member
      · exact calls acc.size x (by simp) v first
    · intro j y member
      exact calls j y (List.mem_cons_of_mem _ member)

private theorem idx_bound {α : Type} {f : Nat → α → Except String Nat}
    {xs : Array α} {ys : Array Nat} (n : Nat) (run : xs.mapIdxM f = .ok ys)
    (calls : ∀ j x,x ∈ xs.toList → ∀ v,f j x = .ok v → v < n) : ∀ v ∈ ys.toList,v < n := by
  have normal : xs.mapIdxM f = List.toArray <$> xs.toList.mapIdxM f := by
    simpa using (List.mapIdxM_toArray (l := xs.toList) (f := f))
  rw [normal] at run
  cases mapped : xs.toList.mapIdxM f with
  | error err => simp only [mapped,Functor.map,Except.map] at run; cases run
  | ok values =>
    simp only [mapped,Functor.map,Except.map,Except.ok.injEq] at run
    subst ys
    simpa using idx_go_bound n xs.toList #[] values mapped (by simp) calls

private theorem successors_bound {source : Array (Array Nat)} {nodes : Array Node}
    {node : Node} {row : Array Nat} (run : successors source nodes node = .ok row) :
    ∀ v ∈ row.toList,v < nodes.size := by
  cases node with
  | edge pred index target =>
    unfold successors at run
    obtain ⟨label,call,run⟩ := Except.bind_ok run
    simp only [pure,Except.pure,Except.ok.injEq] at run
    subst row
    intro v member
    have same : v = label := by simpa using member
    subst v
    exact (Array.getElem?_eq_some_iff.mp (label_lookup call)).1
  | original bi =>
    unfold successors at run
    apply idx_bound nodes.size run
    intro j x _ v call
    split at call <;> exact (Array.getElem?_eq_some_iff.mp (label_lookup call)).1

/-- Every actual computed Stock successor is a valid output node index. This
is derived from the graph label lookups, including all TryCall destinations. -/
theorem stock_lower_graph_bounds {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    result.order.successors.size = result.code.blocks.size ∧
    ∀ (label : Nat) (row : Array Nat),result.order.successors[label]? = some row →
      ∀ v ∈ row.toList,v < result.code.blocks.size := by
  obtain ⟨source,_,graph⟩ := graph_run (stock_lower_order run)
  have count : result.code.blocks.size = result.order.nodes.size :=
    (stock_prepare_dimensions run).1.symm.trans (stock_prepare_dimensions run).2.1
  refine ⟨?_,?_⟩
  · rw [count]
    exact (Prep.amapM_ok graph).1
  · intro label row found v member
    obtain ⟨node,_,mapped⟩ := mapM_lookup graph found
    rw [count]
    exact successors_bound mapped v member

end Backend.Stock.Proof

import Init.Data.Array.MapIdx
import FV.Backend.Proof.StockEntryOrder
import FV.Backend.Proof.StockEdgeCode

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

private theorem idx_go_nonentry {α : Type} {f : Nat → α → Except String Nat} :
    ∀ (xs : List α) (acc : Array Nat) (out : List Nat),List.mapIdxM.go f xs acc = .ok out →
      0 ∉ acc.toList → (∀ j x,x ∈ xs → f j x ≠ .ok 0) → 0 ∉ out
  | [], acc, out, run, initial, calls => by
    simp only [List.mapIdxM.go,pure,Except.pure,Except.ok.injEq] at run
    subst out
    exact initial
  | x :: xs, acc, out, run, initial, calls => by
    simp only [List.mapIdxM.go] at run
    obtain ⟨value,first,rest⟩ := Except.bind_ok run
    have nonzero : value ≠ 0 := by intro zero; rw [zero] at first; exact calls acc.size x (by simp) first
    exact idx_go_nonentry xs (acc.push value) out rest (by simp [initial,Ne.symm nonzero])
      (fun j y hy => calls j y (List.mem_cons_of_mem _ hy))

private theorem idx_nonentry {α : Type} {f : Nat → α → Except String Nat}
    {xs : Array α} {ys : Array Nat} (run : xs.mapIdxM f = .ok ys)
    (calls : ∀ j x,x ∈ xs.toList → f j x ≠ .ok 0) : 0 ∉ ys.toList := by
  have normal : xs.mapIdxM f = List.toArray <$> xs.toList.mapIdxM f := by
    simpa using (List.mapIdxM_toArray (l := xs.toList) (f := f))
  rw [normal] at run
  cases mapped : xs.toList.mapIdxM f with
  | error err => simp only [mapped,Functor.map,Except.map] at run; cases run
  | ok values =>
    simp only [mapped,Functor.map,Except.map,Except.ok.injEq] at run
    subst ys
    simpa using idx_go_nonentry xs.toList #[] values mapped (by simp) calls

private theorem successors_nonentry {source : Array (Array Nat)} {nodes : Array Node}
    (entry : nodes[0]? = some (.original 0))
    (noEdges : ∀ pred index,Node.edge pred index 0 ∉ nodes.toList)
    (noSource : ∀ bi : Nat,0 ∉ source[bi]!.toList) {node : Node} {row : Array Nat}
    (member : node ∈ nodes.toList) (run : successors source nodes node = .ok row) : 0 ∉ row.toList := by
  cases node with
  | edge pred index target =>
    unfold successors at run
    obtain ⟨label,call,run⟩ := Except.bind_ok run
    simp only [pure,Except.pure,Except.ok.injEq] at run
    subst row
    have nonzero : label ≠ 0 := by
      intro zero
      subst label
      have atZero := label_lookup call
      rw [entry] at atZero
      simp only [Option.some.injEq,Node.original.injEq] at atZero
      subst target
      exact noEdges pred index member
    simpa using Ne.symm nonzero
  | original bi =>
    unfold successors at run
    apply idx_nonentry run
    intro k target member call
    have nonzero : target ≠ 0 := by intro zero; rw [zero] at member; exact noSource bi member
    split at call
    · have atZero := label_lookup call
      rw [entry] at atZero
      cases atZero
    · have atZero := label_lookup call
      rw [entry] at atZero
      simp only [Option.some.injEq,Node.original.injEq] at atZero
      exact nonzero atZero.symm

/-- The actual computed Stock graph has no successor label0, across every
original branch/term form and every inserted critical edge. This derives the
graph property from original scope, without a supplied graph certificate. -/
theorem stock_lower_graph_nonentry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∀ (label : Nat) (row : Array Nat),result.order.successors[label]? = some row → 0 ∉ row.toList := by
  have ordered := stock_lower_order run
  obtain ⟨source,computed,graph⟩ := graph_run ordered
  have sourceNoEntry : ∀ bi : Nat,0 ∉ source[bi]!.toList := by
    intro bi
    cases found : source[bi]? with
    | none =>
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,found,Option.getD_none]
      change 0 ∉ ([] : List Nat)
      simp
    | some row =>
      simpa only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,found,Option.getD_some] using
        stock_sourceTable_nonentry computed scope bi row found
  intro label row found
  obtain ⟨node,atNode,mapped⟩ := mapM_lookup graph found
  exact successors_nonentry (stock_blockOrder_entry ordered scope.nonempty)
    (stock_blockOrder_edges_nonentry ordered scope) sourceNoEntry
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atNode)) mapped

end Backend.Stock.Proof

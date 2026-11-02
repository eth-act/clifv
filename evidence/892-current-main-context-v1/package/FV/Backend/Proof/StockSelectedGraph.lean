import Init.Data.Array.MapIdx
import FV.Backend.Proof.LowerLemmas
import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerCert
import FV.Backend.Proof.StockEdgeCode
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def sourceTargets (f : Clif.Function) : Except String (Array (Array Nat)) :=
  f.blocks.toArray.mapM fun b =>
    (destinations b.term).toArray.mapM fun (id, _) =>
      match f.blocks.findIdx? (·.id == id) with
      | some i => pure i
      | none => throw s!"unknown block{id}"
private def graphLabel (nodes : Array Node) (node : Node) : Except String Nat :=
  match nodes.findIdx? (· == node) with
  | some i => pure i
  | none => throw "missing lowered block"
private def graphSuccessors (source : Array (Array Nat)) (nodes : Array Node) : Node → Except String (Array Nat)
  | .edge _ _ s => return #[← graphLabel nodes (.original s)]
  | .original bi => source[bi]!.mapIdxM fun k s =>
    if nodes.contains (.edge bi k s) then graphLabel nodes (.edge bi k s) else graphLabel nodes (.original s)
private theorem graph_run {f : Clif.Function} {order : Order} (run : blockOrder f = .ok order) :
    ∃ source,sourceTargets f = .ok source ∧
      order.nodes.mapM (graphSuccessors source order.nodes) = .ok order.successors := by
  unfold blockOrder at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,by assumption,by assumption⟩
private theorem graphLabel_spec {nodes : Array Node} {node : Node} {label : Nat}
    (run : graphLabel nodes node = .ok label) : nodes[label]? = some node := by
  unfold graphLabel at run
  cases found : nodes.findIdx? (· == node) with
  | none => simp [found] at run
  | some i =>
    simp only [found,pure,Except.pure,Except.ok.injEq] at run
    subst label
    obtain ⟨bound,equal,_⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
    have same : nodes[i] = node := by simpa using equal
    simpa only [Array.getElem?_eq_getElem bound,same]

private theorem list_idx_go {α β : Type} {f : Nat → α → Except String β}
    {xs : List α} {acc : Array β} {ys : List β} (run : List.mapIdxM.go f xs acc = .ok ys) :
    ys.length = acc.size + xs.length ∧
    (∀ j,j < acc.size → ys[j]? = acc[j]?) ∧
    (∀ j x,xs[j]? = some x → ∃ y,f (acc.size+j) x = .ok y ∧ ys[acc.size+j]? = some y) := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.mapIdxM.go,pure,Except.pure,Except.ok.injEq] at run
    subst ys
    exact ⟨by simp,fun j _ => by simp,fun j x h => by simp at h⟩
  | cons x xs ih =>
    simp only [List.mapIdxM.go] at run
    cases call : f acc.size x with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok y =>
      simp only [call,bind,Except.bind] at run
      obtain ⟨length,prelude,selected⟩ := ih run
      refine ⟨by simpa [Array.size_push,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using length,?_,?_⟩
      · intro j bound
        rw [prelude j (by simpa using Nat.lt.step bound),Array.getElem?_push]
        simp [bound,show j ≠ acc.size by omega]
      · intro j a found
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst a
          refine ⟨y,by simpa using call,?_⟩
          rw [Nat.add_zero,prelude acc.size (by simp),Array.getElem?_push]
          simp
        | succ j =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨b,mapped,atIndex⟩ := selected j a found
          exact ⟨b,by simpa [Array.size_push,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using mapped,
            by simpa [Array.size_push,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using atIndex⟩
private theorem array_idx_ok {α β : Type} {f : Nat → α → Except String β}
    {xs : Array α} {ys : Array β} (run : xs.mapIdxM f = .ok ys) :
    ys.size = xs.size ∧ ∀ j x,xs[j]? = some x → ∃ y,f j x = .ok y ∧ ys[j]? = some y := by
  have normal : xs.mapIdxM f = List.toArray <$> xs.toList.mapIdxM f := by
    simpa using (List.mapIdxM_toArray (l := xs.toList) (f := f))
  rw [normal] at run
  cases call : xs.toList.mapIdxM f with
  | error e => simp only [call,Functor.map,Except.map] at run; cases run
  | ok values =>
    simp only [call,Functor.map,Except.map,Except.ok.injEq] at run
    subst ys
    obtain ⟨length,_,selected⟩ := list_idx_go call
    refine ⟨by simpa using length,?_⟩
    intro j x found
    obtain ⟨y,mapped,present⟩ := selected j x (by simpa using found)
    exact ⟨y,by simpa using mapped,by simpa using present⟩
private theorem selected_destination {t : Clif.Terminator} {index : Nat} {bc : Clif.BlockCall}
    (selected : (dests t)[index]? = some bc) :
    (destinations t)[index]? = some (bc.block,bc.args.map Clif.TryArg.val) := by
  have same : destinations t = (dests t).map (fun bc => (bc.block,bc.args.map Clif.TryArg.val)) := by
    cases t <;> simp_all [dests,destinations,List.map_map,Function.comp_def]
  simp only [same,List.getElem?_map,selected,Option.map_some]

private theorem source_selected {f : Clif.Function} {source : Array (Array Nat)}
    (run : sourceTargets f = .ok source) {bi index : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc) :
    ∃ target row,f.blocks.findIdx? (·.id == bc.block) = some target ∧
      source[bi]? = some row ∧ row[index]? = some target := by
  obtain ⟨row,mapped,found⟩ := (array_mapM_ok run).2 bi b (by simpa using block)
  obtain ⟨target,lookup,present⟩ := (array_mapM_ok mapped).2 index _
    (by simpa using selected_destination selected)
  cases identified : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [identified] at lookup; cases lookup
  | some tl =>
    simp only [identified,pure,Except.pure,Except.ok.injEq] at lookup
    subst target
    exact ⟨tl,row,rfl,found,present⟩

/-- Every selected ordinary source successor has an actual lowered graph
successor, directly or via its corresponding synthetic edge. Its target index
and nonentry property follow from whole lowering and original LowerScope. -/
theorem stock_lower_selected_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi index : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (selected : (dests b.term)[index]? = some bc) :
    ∃ target targetLabel,blockIdx? f bc.block = some target ∧ target ≠ 0 ∧
      result.order.successors[label]![index]? = some targetLabel ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge bi index target)) := by
  obtain ⟨source,mapping,graph⟩ := graph_run (stock_lower_order run)
  obtain ⟨target,row,identified,sourceRow,present⟩ := source_selected mapping block selected
  obtain ⟨ss,mapped,found⟩ := (array_mapM_ok graph).2 label _ tag
  unfold graphSuccessors at mapped
  dsimp only at mapped
  have actual : source[bi]! = row := by simp [getElem!_def,sourceRow]
  rw [actual] at mapped
  obtain ⟨targetLabel,call,successor⟩ := (array_idx_ok mapped).2 index target present
  have actualSuccessor : result.order.successors[label]![index]? = some targetLabel := by
    simpa [getElem!_def,found] using successor
  have absent := scope.noEntryPred b (List.mem_of_getElem? block) bc.block
    (edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected)))
  have nonentry : target ≠ 0 := by intro zero; subst target; exact absent identified
  refine ⟨target,targetLabel,identified,nonentry,actualSuccessor,?_⟩
  split at call
  · exact .inr (graphLabel_spec call)
  · exact .inl (graphLabel_spec call)
end Backend.Stock.Proof

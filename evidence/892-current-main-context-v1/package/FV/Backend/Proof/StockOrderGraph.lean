import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.LowerLemmas
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

/-- Successful actual order construction connects every synthetic edge node
with exactly one original target label. -/
theorem stock_lower_edge_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label pred k target : Nat}
    (tag : result.order.nodes[label]? = some (.edge pred k target)) :
    ∃ targetLabel,result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) := by
  obtain ⟨source,_,graph⟩ := graph_run (stock_lower_order run)
  obtain ⟨ss,mapped,found⟩ := (array_mapM_ok graph).2 label _ tag
  unfold graphSuccessors at mapped
  cases call : graphLabel result.order.nodes (.original target) with
  | error e => simp only [call,bind,Except.bind] at mapped; cases mapped
  | ok targetLabel =>
    simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at mapped
    subst ss
    exact ⟨targetLabel,found,graphLabel_spec call⟩
private theorem source_jump {f : Clif.Function} {source : Array (Array Nat)}
    (run : sourceTargets f = .ok source) {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) {bc : Clif.BlockCall} (term : b.term = .jump bc) :
    ∃ target,f.blocks.findIdx? (·.id == bc.block) = some target ∧ source[bi]? = some #[target] := by
  obtain ⟨ss,mapped,found⟩ := (array_mapM_ok run).2 bi b (by simpa using block)
  rw [term] at mapped
  cases target : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp [destinations,Array.mapM_eq_mapM_toList,target] at mapped
  | some tl =>
    have same : ss = #[tl] := by simpa [destinations,Array.mapM_eq_mapM_toList,target] using mapped.symm
    exact ⟨tl,rfl,by simpa only [same] using found⟩

/-- Actual whole-driver jump successors point to the source target, directly
or via the corresponding synthetic edge node. No supplied CFG certificate. -/
theorem stock_lower_jump_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (term : b.term = .jump bc) :
    ∃ target targetLabel,f.blocks.findIdx? (·.id == bc.block) = some target ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge bi 0 target)) := by
  obtain ⟨source,mapping,graph⟩ := graph_run (stock_lower_order run)
  obtain ⟨target,targetFound,row⟩ := source_jump mapping block term
  obtain ⟨ss,mapped,found⟩ := (array_mapM_ok graph).2 label _ tag
  unfold graphSuccessors at mapped
  dsimp only at mapped
  have sourceRow : source[bi]! = #[target] := by simp [getElem!_def,row]
  rw [sourceRow] at mapped
  simp only [Array.mapIdxM,Array.mapFinIdxM,Array.size_singleton,Array.mapFinIdxM.map] at mapped
  change Except.bind (if result.order.nodes.contains (.edge bi 0 target) then
      graphLabel result.order.nodes (.edge bi 0 target) else graphLabel result.order.nodes (.original target))
      (fun next => .ok #[next]) = .ok ss at mapped
  split at mapped
  · cases call : graphLabel result.order.nodes (.edge bi 0 target) with
    | error e => simp only [call,bind,Except.bind] at mapped; cases mapped
    | ok next =>
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at mapped
      subst ss
      exact ⟨target,next,targetFound,found,.inr (graphLabel_spec call)⟩
  · cases call : graphLabel result.order.nodes (.original target) with
    | error e => simp only [call,bind,Except.bind] at mapped; cases mapped
    | ok next =>
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at mapped
      subst ss
      exact ⟨target,next,targetFound,found,.inl (graphLabel_spec call)⟩
/-- The original no-entry-predecessor condition derives nonentry target
classification; it is not a new accepted-input condition. -/
theorem stock_lower_jump_nonentry_successor {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (term : b.term = .jump bc) :
    ∃ target targetLabel,f.blocks.findIdx? (·.id == bc.block) = some target ∧ target ≠ 0 ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      (result.order.nodes[targetLabel]? = some (.original target) ∨
       result.order.nodes[targetLabel]? = some (.edge bi 0 target)) := by
  obtain ⟨target,targetLabel,found,successors,node⟩ := stock_lower_jump_successor run tag block term
  have absent := scope.noEntryPred b (List.mem_of_getElem? block) bc.block
    (by simp [succIds,dests,term])
  have nonentry : target ≠ 0 := by
    intro zero
    subst target
    exact absent found
  exact ⟨target,targetLabel,found,nonentry,successors,node⟩
end Backend.Stock.Proof

import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockReturnScanShape
import FV.Backend.Proof.StockTerminalPlacement
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
private theorem source_terminal {f : Clif.Function} {source : Array (Array Nat)}
    (run : sourceTargets f = .ok source) {bi : Nat} {b : Clif.Block}
    (block : f.blocks[bi]? = some b) (terminal : retOrTrap b.term = true) : source[bi]? = some #[] := by
  obtain ⟨row,mapped,found⟩ := (array_mapM_ok run).2 bi b (by simpa using block)
  cases term : b.term <;> simp only [term,retOrTrap] at terminal
  all_goals try contradiction
  all_goals
    rw [term] at mapped
    have equal : row = #[] := by simpa [destinations,Array.mapM_eq_mapM_toList] using mapped.symm
    simpa only [equal] using found

/-- Actual original return/trap nodes have the empty computed successor row.
This follows from the real source-table and order construction. -/
theorem stock_lower_terminal_successors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat} {b : Clif.Block}
    (node : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (terminal : retOrTrap b.term = true) :
    result.order.successors[label]? = some #[] := by
  obtain ⟨source,computed,graph⟩ := graph_run (stock_lower_order run)
  have row := source_terminal computed block terminal
  obtain ⟨targets,mapped,found⟩ := (array_mapM_ok graph).2 label _ node
  have empty : source[bi]! = #[] := by simp [getElem!_def,row]
  simp only [graphSuccessors,empty] at mapped
  have equal : targets = #[] := by simpa [Array.mapIdxM,Array.mapFinIdxM,Array.mapFinIdxM.map] using mapped.symm
  simpa only [equal] using found

private def resolved (result : Result) :=
  Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)

/-- A complete actual return scan supplies its returned original-node CFG
clause, with empty successors and its final alias-resolved ABI return. -/
theorem stock_lower_return_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) {xs : List Nat}
    (ret : b.term = .ret xs) :
    ∃ (label : Nat) (vb : VBlock) (last : MInst),
      result.order.nodes[label]? = some (.original event.block) ∧
      result.code.blocks[label]? = some vb ∧ vb.insts.back? = some last ∧
      last.isTerminator = true ∧ last.targets = [] ∧ result.order.successors[label]? = some #[] := by
  have rt : retOrTrap f.blocks[event.block]!.term = true := by simp [getElem!_def,block,ret,retOrTrap]
  obtain ⟨label,vb,preludeCode,node,placed,code⟩ := stock_lower_terminal_scan_code run events rt
  obtain ⟨rs,ps,atLast,_⟩ := stock_lower_return_scan_last run scope events block ret
  refine ⟨label,vb,(MInst.rets (rs.zip ps)).mapRegs (resolved result),node,placed,?_,?_,?_,?_⟩
  · rw [code,Array.back?_append,Array.back?_map,atLast]
    rfl
  · rfl
  · rfl
  · exact stock_lower_terminal_successors run node block (by rw [ret]; rfl)

/-- A complete actual trap scan supplies its returned original-node CFG
clause, with the original coded UDF and empty successors. -/
theorem stock_lower_trap_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) {c : Clif.TrapCode}
    (trap : b.term = .trap c) :
    ∃ (label : Nat) (vb : VBlock),result.order.nodes[label]? = some (.original event.block) ∧
      result.code.blocks[label]? = some vb ∧ vb.insts.back? = some (.udf c) ∧
      result.order.successors[label]? = some #[] := by
  have rt : retOrTrap f.blocks[event.block]!.term = true := by simp [getElem!_def,block,trap,retOrTrap]
  obtain ⟨label,vb,preludeCode,node,placed,code⟩ := stock_lower_terminal_scan_code run events rt
  have atLast := stock_lower_trap_scan_last run scope events block trap
  refine ⟨label,vb,node,placed,?_,stock_lower_terminal_successors run node block (by rw [trap]; rfl)⟩
  rw [code,Array.back?_append,Array.back?_map,atLast]
  rfl

end Backend.Stock.Proof

import FV.Backend.Proof.StockOrderGraph

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock assembleOriginalBlock

private theorem outgoingStep_size {ctx : Ctx} {order : Order} {bi : Nat}
    {input output : State × Array (Array Reg)} {target : Nat × Nat}
    (run : outgoingStep ctx order bi input target = .ok output) : output.2.size = input.2.size+1 := by
  unfold outgoingStep at run
  split at run
  · cases run
    simp
  · obtain ⟨pair,_,run⟩ := Except.bind_ok run
    cases pair
    cases run
    simp

private theorem outgoingFold_size {ctx : Ctx} {order : Order} {bi : Nat}
    {xs : List (Nat × Nat)} {input output : State × Array (Array Reg)}
    (run : xs.foldlM (outgoingStep ctx order bi) input = .ok output) :
    output.2.size = input.2.size+xs.length := by
  induction xs generalizing input with
  | nil => cases run; simp
  | cons x xs ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,first,rest⟩ := Except.bind_ok run
    have tail := ih rest
    have head := outgoingStep_size first
    simp only [List.length_cons]
    omega

private theorem collect_size {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {input : State} {output : State × Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets input = .ok output) : output.2.size = targets.size := by
  unfold collectOutgoing at run
  simpa using outgoingFold_size run

private theorem core_size {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.outgoing.size = targets.size := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    exact collect_size (by assumption)

private def RowSize (order : Order) (label : Nat) (row : Array (Array Reg)) : Prop :=
  match order.nodes[label]! with
  | .edge .. => row.size = 1
  | .original .. => row.size = order.successors[label]!.size

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block row,output.blocks = input.blocks.set! label block ∧
      output.edgeArgs = input.edgeArgs.set! label row ∧ RowSize order label row := by
  unfold lowerNode at run
  cases node : order.nodes[label]! with
  | edge pred index target =>
    simp only [node] at run
    obtain ⟨pair,_,run⟩ := Except.bind_ok run
    cases pair
    cases run
    exact ⟨_,_,rfl,rfl,by simp [RowSize,node]⟩
  | original bi =>
    simp only [node] at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    all_goals
      cases run
      exact ⟨_,_,rfl,rfl,by simpa only [RowSize,node] using core_size (by assumption)⟩

private theorem nodes_sizes {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size ∧ output.edgeArgs.size = input.edgeArgs.size ∧
    ∀ (k : Nat) (_hk : k < output.edgeArgs.size),
      (k ∈ labels ∨ RowSize order k input.edgeArgs[k]!) → RowSize order k output.edgeArgs[k]! := by
  induction labels generalizing input with
  | nil => cases run; exact ⟨rfl,rfl,fun _ _ h => h.resolve_left (by simp)⟩
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,step,restRun⟩ := Except.bind_ok run
    obtain ⟨block,row,blocks,rows,rowSize⟩ := node_install step
    have blockSize : middle.blocks.size = input.blocks.size := by rw [blocks]; simp
    have edgeSize : middle.edgeArgs.size = input.edgeArgs.size := by rw [rows]; simp
    obtain ⟨laterBlocks,laterRows,keeps⟩ := ih restRun
    refine ⟨laterBlocks.trans blockSize,laterRows.trans edgeSize,?_⟩
    intro k hk source
    apply keeps k hk
    by_cases future : k ∈ rest
    · exact .inl future
    · right
      have hm : k < middle.edgeArgs.size := by rw [← laterRows]; exact hk
      have hi : k < input.edgeArgs.size := by rw [← edgeSize]; exact hm
      by_cases same : label = k
      · have atRow : middle.edgeArgs[k]? = some row := by
          rw [rows,same,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt hi]
        rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,atRow]
        simpa only [same,Option.getD_some] using rowSize
      · have inherited : RowSize order k input.edgeArgs[k]! := by
          rcases source with member | inherited
          · simp only [List.mem_cons] at member
            rcases member with equal | member
            · exact False.elim (same equal.symm)
            · exact False.elim (future member)
          · exact inherited
        have unchanged : middle.edgeArgs[k]? = input.edgeArgs[k]? := by
          rw [rows]
          simp [Array.set!,same]
        simpa only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,unchanged] using inherited

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem origin {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.code.blocks.size = driver.blocks.size ∧
      result.edgeArgs = driver.edgeArgs.map (fun row => row.map fun rs => rs.map
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by simp,rfl⟩

/-- Every successful actual Stock lowering has one row per returned block and
one vector per computed graph successor. This derives both copy dimensions from
the real traversal/collection/final resolver, with no supplied row certificate. -/
theorem stock_prepare_dimensions {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    result.edgeArgs.size = result.code.blocks.size ∧
    result.edgeArgs.size = result.order.nodes.size ∧
    ∀ (label : Nat) (row : Array (Array Reg)),result.edgeArgs[label]? = some row →
      row.size = result.order.successors[label]!.size := by
  obtain ⟨ranges,params,driver,folded,codeSize,edges⟩ := origin run
  obtain ⟨blocks,rows,shape⟩ := nodes_sizes folded
  have count : result.edgeArgs.size = result.order.nodes.size := by rw [edges,Array.size_map,rows]; simp [startDriver]
  refine ⟨by rw [edges,Array.size_map,codeSize,blocks,rows]; simp [startDriver],count,?_⟩
  intro label row atRow
  have bound := (Array.getElem?_eq_some_iff.mp atRow).1
  have hd : label < driver.edgeArgs.size := by rw [edges,Array.size_map] at bound; exact bound
  have member : label ∈ (Array.range result.order.nodes.size).reverse.toList := by
    simpa using (show label < result.order.nodes.size by rw [← count]; exact bound)
  have actual := shape label hd (.inl member)
  have size : row.size = driver.edgeArgs[label]!.size := by
    rw [edges,Array.getElem?_map,Array.getElem?_eq_getElem hd,Option.map_some,Option.some.injEq] at atRow
    rw [← atRow,Array.size_map,getElem!_pos driver.edgeArgs label hd]
  cases node : result.order.nodes[label]! with
  | original bi => simpa only [RowSize,node,← size] using actual
  | edge pred k target =>
    have hn : label < result.order.nodes.size := by rw [← count]; exact bound
    have tag : result.order.nodes[label]? = some (.edge pred k target) := by
      rw [Array.getElem?_eq_getElem hn]
      rw [getElem!_pos result.order.nodes label hn] at node
      exact congrArg some node
    obtain ⟨targetLabel,successors,_⟩ := stock_lower_edge_successor run tag
    have successorSize : result.order.successors[label]!.size = 1 := by
      rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,successors]
      rfl
    simpa only [RowSize,node,← size,successorSize] using actual

end Backend.Stock.Proof

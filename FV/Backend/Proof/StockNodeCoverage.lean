import FV.Backend.Proof.StockTerminalCfg

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem node_scan {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (node : order.nodes[label]! = .original bi)
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ (data : Backend.V) (core : LoweredBlockCore),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      output.blockScans = input.blockScans.push core.scan := by
  unfold lowerNode at run
  simp only [node] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,_,by assumption,rfl⟩

private theorem node_mono {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    {event : BlockScanEvent} (member : event ∈ input.blockScans.toList) : event ∈ output.blockScans.toList := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    first
    | exact member
    | change event ∈ (input.blockScans.push _).toList
      simp only [Array.toList_push,List.mem_append,List.mem_singleton]
      exact .inl member

private theorem nodes_mono {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    {event : BlockScanEvent} (member : event ∈ input.blockScans.toList) : event ∈ output.blockScans.toList := by
  induction labels generalizing input with
  | nil => cases run; exact member
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,step,rest⟩ := Except.bind_ok run
    exact ih rest (node_mono step member)

private theorem origin {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (starting finishing : DriverState),
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d) starting = .ok finishing ∧
      result.blockScans = finishing.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,_,by assumption,rfl⟩

/-- Every actual original output node has an actual retained whole-block scan.
It is created by that node's real transition and survives the remaining reverse
traversal. No scan-membership certificate is supplied. -/
theorem stock_lower_original_scan {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (node : result.order.nodes[label]? = some (.original bi)) :
    ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi := by
  obtain ⟨ranges,params,starting,finishing,folded,events⟩ := origin run
  have bound := (Array.getElem?_eq_some_iff.mp node).1
  have member : label ∈ (Array.range result.order.nodes.size).reverse.toList := by simpa using bound
  obtain ⟨earlier,suffix,parts,_⟩ := List.eq_append_cons_of_mem member
  rw [parts,List.foldlM_append] at folded
  obtain ⟨before,_,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_cons] at rest
  obtain ⟨after,step,last⟩ := Except.bind_ok rest
  have tag : result.order.nodes[label]! = .original bi := by simp only [getElem!_def,node]
  obtain ⟨data,core,lowered,installed⟩ := node_scan tag step
  have current := (stock_lowerBlockCore_scanOrigin lowered).2.2.1
  refine ⟨core.scan,?_,current⟩
  rw [events]
  apply nodes_mono last
  rw [installed]
  simp

/-- Every actual original return/trap node satisfies the emitted zero-successor
CFG clause at that exact output index. Scan coverage and index uniqueness are
both derived internally from the successful Stock run and original scope. -/
theorem stock_lower_terminal_cfg_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat} {b : Clif.Block}
    (node : result.order.nodes[label]? = some (.original bi))
    (block : f.blocks[bi]? = some b) (terminal : retOrTrap b.term = true) :
    ∃ (vb : VBlock) (last : MInst),result.code.blocks[label]? = some vb ∧
      vb.insts.back? = some last ∧ last.isTerminator = true ∧ last.targets = [] ∧
      result.order.successors[label]? = some #[] := by
  obtain ⟨event,events,current⟩ := stock_lower_original_scan run node
  have source : f.blocks[event.block]? = some b := by rw [current]; exact block
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  cases term : b.term <;> simp only [term,retOrTrap] at terminal
  all_goals try contradiction
  · obtain ⟨label',vb,last,tag,placed,back,ends,targets,successors⟩ := stock_lower_return_cfg run scope events source term
    rw [current] at tag
    have same := stock_blockOrder_original_unique (stock_lower_order run) nonempty tag node
    subst label'
    exact ⟨vb,last,placed,back,ends,targets,successors⟩
  · obtain ⟨label',vb,tag,placed,back,successors⟩ := stock_lower_trap_cfg run scope events source term
    rw [current] at tag
    have same := stock_blockOrder_original_unique (stock_lower_order run) nonempty tag node
    subst label'
    exact ⟨vb,_,placed,back,rfl,rfl,successors⟩

end Backend.Stock.Proof

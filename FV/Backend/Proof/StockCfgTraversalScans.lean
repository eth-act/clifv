import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockLinearCfgTrace
import FV.Backend.Proof.StockSourceOrder

namespace Backend.Stock.Proof.CfgTrace
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] lowerBlockCore assembleOriginalBlock

/-- Every real node preserves all earlier complete scan events. Original nodes
append exactly their own source block; synthetic edges append no block scan. -/
theorem node_scan_append {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ added : List BlockScanEvent,
      output.blockScans.toList = input.blockScans.toList ++ added ∧
      added.map (·.block) = match order.nodes[label]! with
        | .original bi => [bi]
        | .edge .. => [] := by
  cases node : order.nodes[label]! with
  | original bi =>
    obtain ⟨data,core,called,state,scans⟩ := LinearCfg.original_node_scan run node
    refine ⟨[core.scan],?_,?_⟩
    · simp only [scans,Array.toList_push]
    · simp only [List.map_cons,List.map_nil,(stock_lowerBlockCore_scanOrigin called).2.2.1]
  | edge pred index target =>
    unfold lowerNode at run
    simp only [node] at run
    cases called : branchArgs ctx input.state pred index with
    | error message => simp only [called,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,next⟩ := pair
      simp only [called,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact ⟨[],by simp,rfl⟩

private theorem node_scan_mem {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    {event : BlockScanEvent} (member : event ∈ input.blockScans.toList) :
    event ∈ output.blockScans.toList := by
  obtain ⟨added,scans,_⟩ := node_scan_append run
  rw [scans]
  exact List.mem_append_left _ member

private theorem fold_scan_mem {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    {event : BlockScanEvent} (member : event ∈ input.blockScans.toList) :
    event ∈ output.blockScans.toList := by
  induction labels generalizing input with
  | nil => simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run; subst output; exact member
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,called,rest⟩ := Except.bind_ok run
    exact ih rest (node_scan_mem called member)

private theorem fold_scan_blocks {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blockScans.toList.map (·.block) = input.blockScans.toList.map (·.block) ++
      labels.filterMap (fun k => match order.nodes[k]! with | .original bi => some bi | .edge .. => none) := by
  induction labels generalizing input with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run
    subst output
    simp
  | cons label labels ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,called,rest⟩ := Except.bind_ok run
    obtain ⟨added,scans,blocks⟩ := node_scan_append called
    rw [ih rest,scans,List.map_append,blocks,List.append_assoc,List.filterMap_cons]
    cases node : order.nodes[label]! <;> simp

/-- The exact retained source-block sequence follows the one real reverse
traversal, for arbitrary graphs, including inserted synthetic edge nodes. -/
theorem actual_scan_blocks {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    result.blockScans.toList.map (·.block) =
      (Array.range result.order.nodes.size).reverse.toList.filterMap
        (fun k => match result.order.nodes[k]! with | .original bi => some bi | .edge .. => none) := by
  obtain ⟨ranges,params,starting,finishing,build,ordered,initial,empty,folded,events⟩ :=
    LinearCfg.actual_traversal run
  have blocks := fold_scan_blocks folded
  simpa only [events,empty,Array.toList_empty,List.map_nil,List.nil_append] using blocks

private theorem range_nodes {nodes : Array Node} :
    (Array.range nodes.size).map (fun k => nodes[k]!) = nodes := by
  apply Array.ext
  · simp
  · intro k hk hk'
    simp only [Array.getElem_map,Array.getElem_range]
    rw [getElem!_pos nodes k hk']

/-- Retained scans project precisely to reverse source RPO. Critical nodes do
not introduce duplicate source events or change their order. -/
theorem actual_source_scan_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    result.blockScans.toList.map (·.block) = (stockOriginals result.order.nodes).reverse := by
  rw [actual_scan_blocks run]
  have order : (Array.range result.order.nodes.size).reverse.toList.map
      (fun k => result.order.nodes[k]!) = result.order.nodes.toList.reverse := by
    rw [Array.toList_reverse,List.map_reverse,← Array.toList_map,range_nodes]
  let project : Node → Option Nat := fun node => match node with
    | .original bi => some bi | .edge .. => none
  have projected : stockOriginals result.order.nodes = result.order.nodes.toList.filterMap project := by
    unfold stockOriginals
    congr 1
  calc
    _ = ((Array.range result.order.nodes.size).reverse.toList.map
        (fun k => result.order.nodes[k]!)).filterMap project := by
      rw [List.filterMap_map]
      congr 1
    _ = result.order.nodes.toList.reverse.filterMap project := congrArg (List.filterMap project) order
    _ = (stockOriginals result.order.nodes).reverse := by rw [List.filterMap_reverse,← projected]

/-- The actual scan list has one event per reachable original block. -/
theorem actual_scan_blocks_nodup {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    (result.blockScans.toList.map (·.block)).Nodup := by
  rw [actual_source_scan_order run]
  have nonempty : f.blocks.length ≠ 0 := fun h => scope.nonempty (List.length_eq_zero_iff.mp h)
  apply List.pairwise_reverse.mpr
  exact (stock_blockOrder_originals_nodup (stock_lower_order run) nonempty).1.imp Ne.symm

private theorem eq_of_same_block {events : List BlockScanEvent}
    (unique : (events.map (·.block)).Nodup) {first second : BlockScanEvent}
    (fm : first ∈ events) (sm : second ∈ events) (same : first.block = second.block) : first = second := by
  induction events generalizing first second with
  | nil => cases fm
  | cons event events ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp fm with firstEq | firstTail
    · subst first
      rcases List.mem_cons.mp sm with secondEq | secondTail
      · exact secondEq.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨second,secondTail,same.symm⟩))
    · rcases List.mem_cons.mp sm with secondEq | secondTail
      · subst second
        exact False.elim (unique.1 (List.mem_map.mpr ⟨first,firstTail,same⟩))
      · exact ih unique.2 firstTail secondTail same

/-- Independently obtained retained witnesses for the same original block are
the same actual scan, derived from the driver rather than assumed by callers. -/
theorem actual_scan_unique {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {first second : BlockScanEvent} (fm : first ∈ result.blockScans.toList)
    (sm : second ∈ result.blockScans.toList) (same : first.block = second.block) : first = second :=
  eq_of_same_block (actual_scan_blocks_nodup run scope) fm sm same

/-- Two original nodes in the real traversal are connected by the actual
intervening fold. This exposes the exact states needed to transport invariants
across arbitrarily many original or synthetic nodes. -/
theorem actual_ordered_original_cores {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {earlier intervening suffix : List Nat}
    {firstLabel secondLabel firstBlock secondBlock : Nat}
    (labels : (Array.range result.order.nodes.size).reverse.toList =
      earlier ++ firstLabel :: (intervening ++ secondLabel :: suffix))
    (firstTag : result.order.nodes[firstLabel]! = .original firstBlock)
    (secondTag : result.order.nodes[secondLabel]! = .original secondBlock) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input : State)
      (afterFirst beforeSecond : DriverState) (first second : LoweredBlockCore)
      (firstData secondData : Backend.V),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order f f.blocks[firstBlock]! firstBlock
        ranges[firstBlock]!.1 ranges[firstBlock]!.2 firstData
        result.order.successors[firstLabel]! input = .ok first ∧
      lowerBlockCore result.ctx result.order f f.blocks[secondBlock]! secondBlock
        ranges[secondBlock]!.1 ranges[secondBlock]!.2 secondData
        result.order.successors[secondLabel]! beforeSecond.state = .ok second ∧
      afterFirst.state = first.state ∧
      intervening.foldlM (fun d k => lowerNode result.ctx ranges result.order f params k d)
        afterFirst = .ok beforeSecond ∧
      first.scan ∈ result.blockScans.toList ∧ second.scan ∈ result.blockScans.toList := by
  obtain ⟨ranges,params,starting,finishing,build,ordered,initial,empty,folded,events⟩ :=
    LinearCfg.actual_traversal run
  rw [labels,List.foldlM_append] at folded
  obtain ⟨before,prefixRun,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_cons] at rest
  obtain ⟨afterFirst,firstRun,rest⟩ := Except.bind_ok rest
  rw [List.foldlM_append] at rest
  obtain ⟨beforeSecond,interveningRun,rest⟩ := Except.bind_ok rest
  rw [List.foldlM_cons] at rest
  obtain ⟨afterSecond,secondRun,suffixRun⟩ := Except.bind_ok rest
  obtain ⟨firstData,first,firstCore,firstState,firstScans⟩ :=
    LinearCfg.original_node_scan firstRun firstTag
  obtain ⟨secondData,second,secondCore,secondState,secondScans⟩ :=
    LinearCfg.original_node_scan secondRun secondTag
  have firstMember : first.scan ∈ afterFirst.blockScans.toList := by simp [firstScans]
  have secondMember : second.scan ∈ afterSecond.blockScans.toList := by simp [secondScans]
  refine ⟨ranges,params,before.state,afterFirst,beforeSecond,first,second,firstData,secondData,
    build,firstCore,secondCore,firstState,interveningRun,?_,?_⟩
  · simpa only [events] using fold_scan_mem suffixRun
      (node_scan_mem secondRun (fold_scan_mem interveningRun firstMember))
  · simpa only [events] using fold_scan_mem suffixRun secondMember

/-- Adjacent original nodes share the exact state in the one real compiler
traversal. Prefixes and suffixes may contain arbitrary original or synthetic
nodes; no independently chosen core-input equality is assumed. -/
theorem actual_adjacent_original_cores {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {earlier suffix : List Nat}
    {firstLabel secondLabel firstBlock secondBlock : Nat}
    (labels : (Array.range result.order.nodes.size).reverse.toList =
      earlier ++ firstLabel :: secondLabel :: suffix)
    (firstTag : result.order.nodes[firstLabel]! = .original firstBlock)
    (secondTag : result.order.nodes[secondLabel]! = .original secondBlock) :
    ∃ (ranges : Array (Nat × Nat)) (input : State)
      (first second : LoweredBlockCore) (firstData secondData : Backend.V),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order f f.blocks[firstBlock]! firstBlock
        ranges[firstBlock]!.1 ranges[firstBlock]!.2 firstData
        result.order.successors[firstLabel]! input = .ok first ∧
      lowerBlockCore result.ctx result.order f f.blocks[secondBlock]! secondBlock
        ranges[secondBlock]!.1 ranges[secondBlock]!.2 secondData
        result.order.successors[secondLabel]! first.state = .ok second ∧
      first.scan ∈ result.blockScans.toList ∧ second.scan ∈ result.blockScans.toList := by
  obtain ⟨ranges,params,input,afterFirst,beforeSecond,first,second,fd,sd,build,fr,sr,state,gap,fm,sm⟩ :=
    actual_ordered_original_cores run (intervening := []) (by simpa using labels) firstTag secondTag
  simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at gap
  subst beforeSecond
  rw [state] at sr
  exact ⟨ranges,input,first,second,fd,sd,build,fr,sr,fm,sm⟩

end Backend.Stock.Proof.CfgTrace

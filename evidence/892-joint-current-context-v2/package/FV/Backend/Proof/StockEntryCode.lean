import FV.Backend.Proof.StockEntryOrder
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.IselExtern

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem assembled_entry {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b 0 label targets outgoing params uses code = .ok block) :
    block.label = label ∧ block.params = #[] := by
  unfold assembleOriginalBlock at run
  simp only [beq_self_eq_true,ite_true,bind,Except.bind,pure,Except.pure] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨rfl,rfl⟩

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block,output.blocks = input.blocks.set! label block := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,rfl⟩

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,step,rest⟩ := Except.bind_ok run
    obtain ⟨block,installed⟩ := node_install step
    rw [ih rest,installed]
    simp

private theorem node_entry {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {input output : DriverState}
    (tag : order.nodes[0]! = .original 0)
    (run : lowerNode ctx ranges order f params 0 input = .ok output) :
    ∃ block,output.blocks = input.blocks.set! 0 block ∧ block.label = 0 ∧ block.params = #[] := by
  unfold lowerNode at run
  simp only [tag] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨_,rfl,assembled_entry (by assumption)⟩

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem origin {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      blockOrder f = .ok result.order ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.code.blocks = driver.blocks.map (fun b => {b with
        insts := b.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := b.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}) ∧
      sigParamBytes f.sig = .ok params ∧
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      result.blockScans = driver.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by assumption,rfl,by assumption,by assumption,rfl⟩

/-- Actual Stock lowering places original source entry0 at machine label0 and
assembles it without virtual block parameters. Every fact follows from original
scope and real ordering/traversal/assembly/final alias resolution. -/
theorem stock_lower_entry_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    result.order.nodes[0]? = some (.original 0) ∧
      ∃ block,result.code.blocks[0]? = some block ∧ block.label = 0 ∧ block.params = #[] := by
  obtain ⟨ranges,params,driver,ordered,folded,code,_,_,_⟩ := origin run
  have tag := stock_blockOrder_entry ordered scope.nonempty
  have bound := (Array.getElem?_eq_some_iff.mp tag).1
  have member : 0 ∈ (Array.range result.order.nodes.size).reverse.toList := by simpa using bound
  obtain ⟨earlier,suffix,parts,_⟩ := List.eq_append_cons_of_mem member
  have empty : suffix = [] := by simpa using (stock_backward_suffix_split parts).2
  rw [parts,List.foldlM_append] at folded
  obtain ⟨before,prelude,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_cons] at rest
  obtain ⟨after,step,rest⟩ := Except.bind_ok rest
  rw [empty,List.foldlM_nil] at rest
  cases rest
  have node : result.order.nodes[0]! = .original 0 := by
    rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,tag]
    rfl
  obtain ⟨block,installed,labelled,parameterless⟩ := node_entry node step
  have inBounds : 0 < before.blocks.size := by rw [nodes_size prelude]; simpa [startDriver] using bound
  have atBlock : driver.blocks[0]? = some block := by
    rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt inBounds]
  refine ⟨tag,{block with
    insts := block.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
    params := block.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
    branchArgs := block.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))},
    ?_,labelled,?_⟩
  · simp only [code,Array.getElem?_map,atBlock,Option.map_some]
  · simp [parameterless]

private theorem node_entry_assembly {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {input output : DriverState}
    (tag : order.nodes[0]! = .original 0)
    (run : lowerNode ctx ranges order f params 0 input = .ok output) :
    ∃ (data : Backend.V) (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore ctx order f f.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
        data order.successors[0]! input.state = .ok core ∧
      assembleOriginalBlock ctx f f.blocks[0]! 0 0 order.successors[0]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      output.blocks = input.blocks.set! 0 block ∧ core.scan ∈ output.blockScans.toList := by
  unfold lowerNode at run
  simp only [tag] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨_,_,_,by assumption,by assumption,rfl,by simp [recordCore]⟩

/-- The actual whole-driver entry block comes from the original entry
constructor, with the checked signature widths and a retained real scan.
Final alias resolution is explicit so callers can prove its semantic effect. -/
theorem stock_lower_entry_assembly {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (before : DriverState)
      (data : Backend.V) (core : LoweredBlockCore) (raw block : VBlock),
      sigParamBytes f.sig = .ok params ∧
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      lowerBlockCore result.ctx result.order f f.blocks[0]! 0 ranges[0]!.1 ranges[0]!.2
        data result.order.successors[0]! before.state = .ok core ∧
      assembleOriginalBlock result.ctx f f.blocks[0]! 0 0 result.order.successors[0]!
        core.outgoing params core.state.uses core.code = .ok raw ∧
      core.scan ∈ result.blockScans.toList ∧ result.code.blocks[0]? = some block ∧
      block = {raw with
        insts := raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias
          (result.final.alias.size+1)))
        params := raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨ranges,params,driver,ordered,folded,code,sizes,build,events⟩ := origin run
  have tag := stock_blockOrder_entry ordered scope.nonempty
  have bound := (Array.getElem?_eq_some_iff.mp tag).1
  have member : 0 ∈ (Array.range result.order.nodes.size).reverse.toList := by simpa using bound
  obtain ⟨earlier,suffix,parts,_⟩ := List.eq_append_cons_of_mem member
  have empty : suffix = [] := by simpa using (stock_backward_suffix_split parts).2
  rw [parts,List.foldlM_append] at folded
  obtain ⟨before,prelude,rest⟩ := Except.bind_ok folded
  rw [List.foldlM_cons] at rest
  obtain ⟨after,step,rest⟩ := Except.bind_ok rest
  rw [empty,List.foldlM_nil] at rest
  cases rest
  have node : result.order.nodes[0]! = .original 0 := by
    rw [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,tag]
    rfl
  obtain ⟨data,core,raw,coreRun,assembled,installed,scan⟩ := node_entry_assembly node step
  have inBounds : 0 < before.blocks.size := by rw [nodes_size prelude]; simpa [startDriver] using bound
  have atBlock : driver.blocks[0]? = some raw := by
    rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt inBounds]
  refine ⟨ranges,params,before,data,core,raw,_,sizes,build,coreRun,assembled,?_,?_,rfl⟩
  · simpa only [events] using scan
  · simp only [code,Array.getElem?_map,atBlock,Option.map_some]

end Backend.Stock.Proof

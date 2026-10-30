import FV.Backend.Proof.StockBranchCfg
import FV.Backend.Proof.StockEmittedGraph
import FV.Backend.Proof.StockGraphBounds
import FV.Backend.Proof.LowerLemmas

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block, output.blocks = input.blocks.set! label block := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨_,rfl⟩

private theorem node_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    output.blocks.size = input.blocks.size := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp

private theorem node_frame {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label other : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) (different : other ≠ label) :
    output.blocks[other]? = input.blocks[other]? := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp [Ne.symm different]

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [call,bind,Except.bind] at run
      exact (ih run).trans (node_size call)

private theorem nodes_frame {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {other : Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    (different : ∀ k ∈ labels,other ≠ k) : output.blocks[other]? = input.blocks[other]? := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [call,bind,Except.bind] at run
      exact (ih run (fun k member => different k (List.mem_cons_of_mem _ member))).trans
        (node_frame call (different label (by simp)))

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem lower_code_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      blockOrder f = .ok result.order ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.blockScans = driver.blockScans ∧ result.final = driver.state ∧
      result.code.blocks = driver.blocks.map (fun b => {b with
        insts := b.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := b.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by assumption,by assumption,rfl,rfl,rfl⟩


private theorem node_original_assembled {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .original bi) :
    ∃ (data : Backend.V) (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      output.blocks = input.blocks.set! label block := by
  let fetchData : Except String Backend.V := match f.blocks[bi]!.term with
    | .tryCall .. | .tryCallIndirect .. => tryCallData f f.blocks[bi]!.term
    | _ => termData (abiTerm f f.blocks[bi]!.term)
  let reject : Bool := (match f.blocks[bi]!.term with | .ret .. => true | _ => false) &&
    (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
  have normal : lowerNode ctx ranges order f params label input = (do
      let data ← fetchData
      if reject then throw "sret parameter is not an entry-block parameter"
      let core ← lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state
      let block ← assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code
      pure { recordCore input core bi ranges[bi]!.2 with
        blocks := input.blocks.set! label block,
        edgeArgs := input.edgeArgs.set! label core.outgoing }) := by
    unfold lowerNode
    simp only [node]
    dsimp only [fetchData, reject]
    split <;> simp_all only [reject] <;> rfl
  rw [normal] at run
  cases dataRun : fetchData with
  | error e => simp only [dataRun, bind, Except.bind] at run; cases run
  | ok data =>
    simp only [dataRun, bind, Except.bind] at run
    split at run
    · cases run
    · cases coreRun : lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state with
      | error e => simp only [coreRun] at run; cases run
      | ok core =>
        simp only [coreRun] at run
        cases assembled : assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
          core.outgoing params core.state.uses core.code with
        | error e => simp only [assembled] at run; cases run
        | ok block =>
          simp only [assembled, pure, Except.pure] at run
          cases run
          exact ⟨data,core,block,coreRun,assembled,rfl⟩

private theorem original_block_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input : State) (data : Backend.V)
      (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! input = .ok core ∧
      assembleOriginalBlock result.ctx f f.blocks[bi]! bi label result.order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      result.code.blocks[label]? = some {block with
        insts := block.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := block.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := block.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨ranges,params,driver,build,ordered,folded,events,final,blocks⟩ := lower_code_origin run
  have bound := (Array.getElem?_eq_some_iff.mp tag).1
  have member : label ∈ (Array.range result.order.nodes.size).reverse.toList := by simpa using bound
  obtain ⟨earlier,suffix,parts,noEarlier⟩ := List.eq_append_cons_of_mem member
  rw [parts,List.foldlM_append] at folded
  cases first : earlier.foldlM (fun d k => lowerNode result.ctx ranges result.order f params k d)
      (startDriver result.initial result.order.nodes.size) with
  | error e => simp only [first,bind,Except.bind] at folded; cases folded
  | ok before =>
    simp only [first,bind,Except.bind] at folded
    rw [List.foldlM_cons] at folded
    cases step : lowerNode result.ctx ranges result.order f params label before with
    | error e => simp only [step,bind,Except.bind] at folded; cases folded
    | ok after =>
      simp only [step,bind,Except.bind] at folded
      have node : result.order.nodes[label]! = .original bi := by
        simp only [getElem!_def,tag]
      obtain ⟨data,core,block,coreRun,assembled,installed⟩ := node_original_assembled step node
      have beforeBound : label < before.blocks.size := by
        rw [nodes_size first]
        simpa only [startDriver,Array.size_replicate] using bound
      have afterBlock : after.blocks[label]? = some block := by
        rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt beforeBound]
      have finalBlock : driver.blocks[label]? = some block := by
        rw [nodes_frame folded,afterBlock]
        intro k member
        rw [(stock_backward_suffix_split parts).2] at member
        have small : k < label := by simpa using member
        omega
      exact ⟨ranges,params,before.state,data,core,block,coreRun,assembled,
        by simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some]⟩

private theorem assemble_suffix {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    ∃ preludeCode : Array MInst, block.insts = preludeCode ++ code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    first | exact ⟨_,rfl⟩ | exact ⟨#[],by simp⟩


private theorem term_map (g : Reg → Reg) (t : MInst) :
    (t.mapRegs g).isTerminator = t.isTerminator := by cases t <;> rfl

/-- Every actual original TryCall block ends in a real terminator whose targets
are exactly its computed Stock graph row, after assembly, reverse traversal and
final alias resolution. No ISLE-run or emitted-code shape premise is supplied. -/
theorem stock_lower_try_targets {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (node : result.order.nodes[label]? = some (.original bi))
    (isTry : f.blocks[bi]!.term.isTry = true) :
    ∃ (block : VBlock) (last : MInst),result.code.blocks[label]? = some block ∧
      block.insts.back? = some last ∧ last.isTerminator = true ∧
      last.targets = result.order.successors[label]!.toList := by
  obtain ⟨ranges,params,input,data,core,block,lowered,assembled,placed⟩ := original_block_origin run node
  obtain ⟨last,atLast,terminal,targets⟩ := stock_lowerBlockCore_try_targets isTry lowered
  obtain ⟨preludeCode,code⟩ := assemble_suffix assembled
  have atBlock : block.insts.back? = some last := by
    rw [code,Array.back?_append,atLast]
    rfl
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨_,last.mapRegs resolve,placed,?_,?_,?_⟩
  · simp only [Array.back?_map,atBlock,Option.map_some,resolve]
  · rw [term_map,terminal]
  · rw [targets_mapRegs,targets]

/-- Every actual original TryCall node satisfies its complete CFG clause,
including the computed row and the actual emitted target-label lookups. -/
theorem stock_lower_try_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat}
    (node : result.order.nodes[label]? = some (.original bi))
    (isTry : f.blocks[bi]!.term.isTry = true) :
    ∃ (block : VBlock) (t : MInst) (row : Array Nat),
      result.code.blocks[label]? = some block ∧ block.insts.back? = some t ∧
      t.isTerminator = true ∧ result.order.successors[label]? = some row ∧
      row.size = t.targets.length ∧
      ∀ (j : Nat) (l : Label),t.targets[j]? = some l →
        ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k := by
  obtain ⟨block,t,placed,atLast,terminal,targets⟩ := stock_lower_try_targets run node isTry
  obtain ⟨count,bounds⟩ := stock_lower_graph_bounds run
  have index : label < result.order.successors.size := by
    rw [count]
    exact (Array.getElem?_eq_some_iff.mp placed).1
  let row := result.order.successors[label]
  have atRow : result.order.successors[label]? = some row := Array.getElem?_eq_getElem index
  have rowEq : result.order.successors[label]! = row := by simp only [getElem!_pos result.order.successors label index]; rfl
  rw [rowEq] at targets
  refine ⟨block,t,row,placed,atLast,terminal,atRow,?_,?_⟩
  · rw [targets,Array.length_toList]
  · intro j l atTarget
    rw [targets] at atTarget
    have atValue : row[j]? = some l := by simpa only [Array.getElem?_toList] using atTarget
    have bound := bounds label row atRow l (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atValue))
    exact ⟨l,atValue,Prep.lab_of (stock_prepare_domain run scope).2 bound
      (stock_lower_dense_labels run l bound)⟩

end Backend.Stock.Proof

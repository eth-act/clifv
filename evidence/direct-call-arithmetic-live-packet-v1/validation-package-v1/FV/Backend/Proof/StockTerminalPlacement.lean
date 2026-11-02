import FV.Backend.Proof.IselContract
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.IselExtern

/-! Placement of actual scan code in the assembled whole-driver output.
Entry materialization is a prefix and later reverse-traversal nodes frame
already installed blocks. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs

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

private theorem core_scan_block {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.scan.block = bi := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

private theorem core_code_terminal {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (terminal : retOrTrap b.term = true)
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    core.code = core.scan.output.code := by
  cases term : b.term <;> simp only [term,retOrTrap] at terminal
  all_goals try contradiction
  all_goals
    unfold lowerBlockCore at run
    simp only [term,Bool.false_eq_true,ite_false] at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    all_goals cases run; simp

private theorem node_new_scan_code {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params : List Nat} {label : Nat}
    {input output : DriverState} {event : BlockScanEvent}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (member : event ∈ output.blockScans.toList)
    (new : event ∉ input.blockScans.toList)
    (terminal : retOrTrap f.blocks[event.block]!.term = true) :
    ∃ (block : VBlock) (preludeCode : Array MInst),
      output.blocks = input.blocks.set! label block ∧
      block.insts = preludeCode ++ event.output.code ∧ order.nodes[label]! = .original event.block := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases args : branchArgs ctx input.state pred k with
    | error e => simp only [args, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [args, bind, Except.bind, pure, Except.pure] at run
      cases run
      exact False.elim (new member)
  | original bi =>
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
            change event ∈ (input.blockScans.push core.scan).toList at member
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
            rcases member with old | same
            · exact False.elim (new old)
            · subst event
              obtain ⟨preludeCode,assembledCode⟩ := assemble_suffix assembled
              have current := core_scan_block coreRun
              rw [current] at terminal
              have coreCode := core_code_terminal terminal coreRun
              refine ⟨block,preludeCode,rfl,?_,?_⟩
              · simp only [assembledCode,coreCode]
              · simpa only [current] using node


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

private theorem new_scan_code_origin {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState} {event : BlockScanEvent}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    (member : event ∈ output.blockScans.toList) (new : event ∉ input.blockScans.toList)
    (terminal : retOrTrap f.blocks[event.block]!.term = true) :
    ∃ (earlier suffix : List Nat) (label : Nat) (before after : DriverState)
      (block : VBlock) (preludeCode : Array MInst),
      labels = earlier ++ label :: suffix ∧
      earlier.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok before ∧
      suffix.foldlM (fun d k => lowerNode ctx ranges order f params k d) after = .ok output ∧
      after.blocks = before.blocks.set! label block ∧
      block.insts = preludeCode ++ event.output.code ∧ order.nodes[label]! = .original event.block := by
  induction labels generalizing input with
  | nil =>
    cases run
    exact False.elim (new member)
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [call,bind,Except.bind] at run
      by_cases now : event ∈ middle.blockScans.toList
      · obtain ⟨block,preludeCode,installed,code,tag⟩ := node_new_scan_code call now new terminal
        exact ⟨[],rest,label,input,middle,block,preludeCode,rfl,rfl,run,installed,code,tag⟩
      · obtain ⟨earlier,suffix,k,before,after,block,preludeCode,
          parts,first,last,installed,code,tag⟩ := ih run now
        refine ⟨label :: earlier,suffix,k,before,after,block,preludeCode,?_,?_,last,installed,code,tag⟩
        · simp only [List.cons_append,parts]
        · simpa only [List.foldlM_cons,call,bind,Except.bind] using first

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem lower_code_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
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
  exact ⟨_,_,_,by assumption,by assumption,rfl,rfl,rfl⟩

/-- An actual return/trap scan is the complete suffix of its returned block,
after entry materialization and final alias resolution. Its original node and
label are derived from the complete real traversal. -/
theorem stock_lower_terminal_scan_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList)
    (terminal : retOrTrap f.blocks[event.block]!.term = true) :
    ∃ (label : Nat) (block : VBlock) (preludeCode : Array MInst),
      result.order.nodes[label]? = some (.original event.block) ∧
      result.code.blocks[label]? = some block ∧
      block.insts = preludeCode ++ event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
  obtain ⟨ranges,params,driver,build,folded,events,final,blocks⟩ := lower_code_origin run
  rw [events] at member
  obtain ⟨earlier,suffix,label,before,after,block,preludeCode,
    parts,first,last,installed,code,tag⟩ := new_scan_code_origin folded member (by simp [startDriver]) terminal
  have split := stock_backward_suffix_split parts
  have bound : label < before.blocks.size := by
    rw [nodes_size first]
    simpa only [startDriver,Array.size_replicate] using split.1
  have afterBlock : after.blocks[label]? = some block := by
    rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  have finalBlock : driver.blocks[label]? = some block := by
    rw [nodes_frame last,afterBlock]
    intro k member
    rw [split.2] at member
    have small : k < label := by simpa using member
    omega
  have atNode : result.order.nodes[label]? = some (.original event.block) := by
    rw [getElem!_pos result.order.nodes label split.1] at tag
    rw [Array.getElem?_eq_getElem split.1,tag]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨label,{block with
      insts := block.insts.map (·.mapRegs resolve)
      params := block.params.map resolve
      branchArgs := block.branchArgs.map resolve},preludeCode.map (·.mapRegs resolve),atNode,?_,?_⟩
  · simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some,resolve]
  · simp only [code,Array.map_append,resolve]

end Backend.Stock.Proof

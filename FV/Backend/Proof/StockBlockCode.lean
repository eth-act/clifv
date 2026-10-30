import FV.Backend.Proof.StockBlockScan
import FV.Backend.Proof.StockTraversalRecordOrigin
import FV.Backend.Proof.StockCoreScanOrigin
import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.LowerSeq

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
  simp [Array.getElem?_setIfInBounds,Ne.symm different]

private theorem core_code {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ afterCode, core.code = core.scan.output.code ++ afterCode := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,rfl⟩

private theorem node_new_scan_code {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params : List Nat} {label : Nat}
    {input output : DriverState} {event : BlockScanEvent}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (member : event ∈ output.blockScans.toList)
    (new : event ∉ input.blockScans.toList) :
    ∃ (block : VBlock) (preludeCode afterCode : Array MInst),
      output.blocks = input.blocks.set! label block ∧
      block.insts = preludeCode ++ event.output.code ++ afterCode := by
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
              obtain ⟨afterCode,coreCode⟩ := core_code coreRun
              refine ⟨block,preludeCode,afterCode,rfl,?_⟩
              simp only [assembledCode,coreCode,Array.append_assoc]


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
    (member : event ∈ output.blockScans.toList) (new : event ∉ input.blockScans.toList) :
    ∃ (earlier suffix : List Nat) (label : Nat) (before after : DriverState)
      (block : VBlock) (preludeCode afterCode : Array MInst),
      labels = earlier ++ label :: suffix ∧
      earlier.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok before ∧
      suffix.foldlM (fun d k => lowerNode ctx ranges order f params k d) after = .ok output ∧
      after.blocks = before.blocks.set! label block ∧
      block.insts = preludeCode ++ event.output.code ++ afterCode := by
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
      · obtain ⟨block,preludeCode,afterCode,installed,code⟩ := node_new_scan_code call now new
        exact ⟨[],rest,label,input,middle,block,preludeCode,afterCode,rfl,rfl,run,installed,code⟩
      · obtain ⟨earlier,suffix,k,before,after,block,preludeCode,afterCode,
          parts,first,last,installed,code⟩ := ih run now
        refine ⟨label :: earlier,suffix,k,before,after,block,preludeCode,afterCode,?_,?_,last,installed,code⟩
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

/-- Every actual original-block scan is placed inside an assembled block of
the returned VCode after final alias resolution. Entry materialization is a
prefix, branch emission a suffix, and later traversal nodes preserve the slot. -/
theorem stock_lower_block_scan_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList) :
    ∃ (label : Nat) (block : VBlock) (preludeCode afterCode : Array MInst),
      result.code.blocks[label]? = some block ∧
      block.insts = preludeCode ++ event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ afterCode := by
  obtain ⟨ranges,params,driver,build,folded,events,final,blocks⟩ := lower_code_origin run
  rw [events] at member
  obtain ⟨earlier,suffix,label,before,after,block,preludeCode,afterCode,
    parts,first,last,installed,code⟩ := new_scan_code_origin folded member (by simp [startDriver])
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
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨label,{block with
      insts := block.insts.map (·.mapRegs resolve)
      params := block.params.map resolve
      branchArgs := block.branchArgs.map resolve},
      preludeCode.map (·.mapRegs resolve),afterCode.map (·.mapRegs resolve),?_,?_⟩
  · simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some,resolve]
  · simp only [code,Array.map_append,resolve]

private theorem scan_record_factor {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan} {record : ScanRecord}
    (cert : ScansSpec exec indices input output) (member : record ∈ output.records) :
    ∃ preludeCode afterCode : Array MInst,
      output.code = preludeCode ++ record.output.emitted ++ afterCode := by
  obtain ⟨before,after,parts⟩ := List.eq_append_cons_of_mem (List.mem_reverse.mpr member)
  refine ⟨(before.flatMap (fun r => r.output.emitted.toList)).toArray,
    (after.flatMap (fun r => r.output.emitted.toList)).toArray,?_⟩
  apply Array.toList_inj.mp
  simp only [cert.code,parts,List.flatMap_append,List.flatMap_cons,Array.toList_append,List.toList_toArray,List.append_assoc]

/-- Every actual retained record's emitted chunk is in the returned VCode,
including entry materialization, branch suffixes and the final alias map. -/
theorem stock_lower_record_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    ∃ (label : Nat) (block : VBlock) (preludeCode afterCode : Array MInst),
      result.code.blocks[label]? = some block ∧
      block.insts = preludeCode ++ record.output.emitted.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ afterCode := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,first,nodeRun,last,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have scanned := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  rw [← eventEq] at scanned
  unfold scanBlock at scanned
  obtain ⟨recordBefore,recordAfter,recordCode⟩ := scan_record_factor (runScans_spec scanned) records
  obtain ⟨label,block,preludeCode,afterCode,placed,code⟩ := stock_lower_block_scan_code run events
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨label,block,preludeCode ++ recordBefore.map (·.mapRegs resolve),
    recordAfter.map (·.mapRegs resolve) ++ afterCode,placed,?_⟩
  simp only [code,recordCode,Array.map_append,Array.append_assoc,resolve]

private theorem segment_of_factor {block : VBlock} {preludeCode code afterCode : Array MInst}
    (parts : block.insts = preludeCode ++ code ++ afterCode) : SegAt block preludeCode.size code.toList := by
  intro k hk
  have bound : k < code.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- The concrete segment-position premise required by VCode simulation is
derived from successful whole Stock lowering and actual record membership. -/
theorem stock_lower_record_segment {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {record : ScanRecord}
    (records : record ∈ event.output.records) :
    ∃ (label : Nat) (block : VBlock) (k : Nat), result.code.blocks[label]? = some block ∧
      SegAt block k (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) := by
  obtain ⟨label,block,preludeCode,afterCode,placed,code⟩ := stock_lower_record_code run events records
  exact ⟨label,block,preludeCode.size,placed,by simpa only [Array.toList_map] using segment_of_factor code⟩
end Backend.Stock.Proof

import FV.Backend.Proof.StockAcquireForwardProducerOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual whole-driver assembly preserves the relative order of both complete retained chunks. -/
theorem stock_lower_records_code_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {first second : ScanRecord} {pre middle post : List ScanRecord}
    (parts : event.output.records.reverse = pre++first::(middle++second::post)) :
    ∃ (label : Nat) (block : VBlock) (beforeCode betweenCode afterCode : Array MInst),
      result.code.blocks[label]? = some block ∧
      block.insts = beforeCode ++ first.output.emitted.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ betweenCode ++
        second.output.emitted.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ afterCode := by
  obtain ⟨label,block,preludeCode,afterCode,found,code⟩ := stock_lower_block_scan_code run events
  obtain ⟨groups,frontiers,exactSunk,assembly⟩ := stock_lower_event_record_frontiers run events
  let preCode : Array MInst := (pre.flatMap (fun record => record.output.emitted.toList)).toArray
  let middleCode : Array MInst := (middle.flatMap (fun record => record.output.emitted.toList)).toArray
  let postCode : Array MInst := (post.flatMap (fun record => record.output.emitted.toList)).toArray
  have scanCode : event.output.code = preCode ++ first.output.emitted ++ middleCode ++ second.output.emitted ++ postCode := by
    apply Array.toList_inj.mp
    simpa only [assembly,parts,List.flatMap_append,List.flatMap_cons,Array.toList_append,List.toList_toArray,
      List.append_assoc,preCode,middleCode,postCode]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨label,block,preludeCode++preCode.map (·.mapRegs resolve),middleCode.map (·.mapRegs resolve),
    postCode.map (·.mapRegs resolve)++afterCode,found,?_⟩
  simp only [code,scanCode,Array.map_append,Array.append_assoc,resolve]

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockMaskBlockRecords
import FV.Backend.Proof.StockGuardedOmission

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Use the exact body split from a jump specification. Original NOP syntax
derives its guarded execution without a global source-format restriction. -/
theorem stock_nop_body_of_split {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  have each : ∀ record ∈ body.records,ScanFallRefines
      (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events
      split member statement current (nops stm (List.mem_of_getElem? statement))
    exact stock_lower_omitted_scan_fall_refines run scope dominated events
      (split.retained record member) split.block statement current recorded omitted
  intro s s' steps ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

end Backend.Stock.Memory

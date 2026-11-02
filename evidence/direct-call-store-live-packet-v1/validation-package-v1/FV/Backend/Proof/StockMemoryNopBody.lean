import FV.Backend.Proof.StockMaskBlockRecords
import FV.Backend.Proof.StockGuardedOmission

/-! UNVALIDATED next-batch source. The frozen production packet excludes this file.
Derive the entry NOP body from actual omitted records. Memory instructions in
other original blocks do not add a global format restriction. -/
namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original NOP syntax derives guarded execution of the actual body. -/
theorem stock_nop_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := Option.some.inj (split.block.symm.trans block)
  subst original
  have each : ∀ record ∈ body.records,ScanFallRefines
      (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events
      split member statement current (nops stm (List.mem_of_getElem? statement))
    exact stock_lower_omitted_scan_fall_refines run scope dominated events
      (split.retained record member) split.block statement current recorded omitted
  refine ⟨term,body,split,?_⟩
  intro s s' steps ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

end Backend.Stock.Memory

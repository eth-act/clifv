import FV.Backend.Proof.StockMemoryNopBody
import FV.Backend.Proof.StockLocalSourceTrap
import FV.Backend.Proof.StockArithmeticBodyRefines

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- NOP body syntax supplies normal and trap composition without restricting successor blocks. -/
theorem stock_nop_body_with_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') ∧
      (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
        (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s code →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          TrapRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  obtain ⟨term,body,split,normal⟩ := stock_nop_body run scope dominated events block nops
    (isem := isem) (MR := MR) (env := env) (cp := cp)
  have each : ∀ record ∈ body.records,ScanFallRefines
      (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events
      split member statement current (nops stm (List.mem_of_getElem? statement))
    exact stock_lower_omitted_scan_fall_refines run scope dominated events
      (split.retained record member) split.block statement current recorded omitted
  have traps : ∀ record ∈ body.records,LocalScanTrapRefines
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member s code failed ρ w held
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    obtain ⟨index,other,inst,rest,otherSource,otherClif,remaining,trapped⟩ := failed
    have same : other = info := Option.some.inj (otherSource.symm.trans source)
    subst other
    have nop : inst = .nop :=
      (Option.some.inj (otherClif.symm.trans clif)).trans (nops stm (List.mem_of_getElem? statement))
    subst inst
    cases trapped
  refine ⟨term,body,split,normal,?_⟩
  intro s code source ρ w held
  apply split.scanned.local_trap_refines each traps s code
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

end Backend.Stock.Memory

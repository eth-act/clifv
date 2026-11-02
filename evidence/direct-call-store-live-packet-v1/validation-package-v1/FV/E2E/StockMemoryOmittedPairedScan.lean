import FV.E2E.StockMemoryPairedScan
import FV.Backend.Proof.StockGuardedOmission

/-! UNVALIDATED next-batch draft. Excluded from frozen production source. -/
namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory Isle
set_option autoImplicit false
set_option Elab.async false

/-- Reuse the existing original-source omission proof in both worlds. An
actual omission emits no code and preserves source memory, so initialized-world
agreement survives without an extra accepted-input condition. -/
theorem stock_lower_omitted_paired_scan
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi+j)
    (executed : scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output)
    {step : Step} (recorded : record.output.step = some step) (omitted : step.decision = .omitted)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) (pairSem (csem Γ.F fc X))
      result.final.alias (PairedScanRel f result event.ctx bi Γ c D) record := by
  intro s s' sourceIndex ρ q before
  obtain ⟨held,otherHeld,worlds⟩ := before
  have facts := scan_omitted executed recorded omitted
  have code : record.output.emitted = #[] := facts.2.2.2.2.2.2.2.1
  have single := stock_lower_omitted_scan_fall_refines run scope dominated events records
    block statement current recorded omitted (isem := csem Γ.F fc X) (MR := RelW Γ f c)
    (env := env) (cp := cp)
  obtain ⟨firstRegs,firstWorld,first,post⟩ := single s s' sourceIndex ρ q.1 held
  obtain ⟨otherRegs,otherWorld,second,otherPost⟩ := single s s' sourceIndex ρ q.2 otherHeld
  have firstEq : SeqEnd.fall ρ q.1 = SeqEnd.fall firstRegs firstWorld := by
    apply Option.some.inj
    simpa only [code,Array.toList_empty,List.map_nil,seqRun] using first
  have secondEq : SeqEnd.fall ρ q.2 = SeqEnd.fall otherRegs otherWorld := by
    apply Option.some.inj
    simpa only [code,Array.toList_empty,List.map_nil,seqRun] using second
  obtain ⟨file,world⟩ := SeqEnd.fall.inj firstEq
  obtain ⟨otherFile,otherWorldEq⟩ := SeqEnd.fall.inj secondEq
  rw [← file,← world] at post
  rw [← otherFile,← otherWorldEq] at otherPost
  obtain ⟨info,inst,vals,regs,rest,source,clif,body,outcome,set,updated⟩ := sourceIndex.2.2
  have memory := (scan_omitted_semantic (ρ := fun k => ρ (aliasNum result.final.alias k))
    executed recorded omitted source clif set).2.1 _ _ outcome
  refine ⟨ρ,q,?_,post,otherPost,?_⟩
  · simp only [code,Array.toList_empty,List.map_nil,seqRun]
  · simpa only [memory] using worlds

end E2E.StockMemory

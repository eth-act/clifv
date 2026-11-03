import FV.Backend.Proof.StockAcquireEmptyMarksPairedFrontier
import FV.Backend.Proof.StockAcquireSourcePrefixBoundary
import FV.Backend.Proof.StockAcquirePairedFrontierInitialization

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Actual backward scan records compose forward source history and paired execution.
Every local semantic obligation must be discharged internally before a public compiler wrapper uses this theorem. -/
theorem scans_paired_read_frontier {f : Clif.Function} {result : Result} {event : BlockScanEvent}
    {env : Clif.Env} {program : Clif.Program} {MR : MemRelT} {Z : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    {entry : Clif.Frame × Clif.Mem} {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output)
    (localRuns : ∀ record ∈ output.records,∀ (prefixRecords : List ScanRecord) (before after : SourcePoint),
      IndexedSourceInst env program f event.ctx event.block record.inst before after →
      ∀ (regs : Nat → CV) (worlds : W2),
      PairedReadFrontierAt f result event env program MR Z entry prefixRecords record.output.state before regs worlds →
      ∃ nextRegs nextWorlds,∃ post : PairedReadFrontierAt f result event env program MR Z entry
        (prefixRecords++[record]) record.input after nextRegs nextWorlds,
        seqRun (pairSem isem) (record.output.emitted.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall nextRegs nextWorlds)) :
    ∀ (prefixRecords : List ScanRecord) (before after : SourcePoint),
      SourceSteps (IndexedSourceInst env program f event.ctx event.block) indices.reverse before after →
      ∀ (regs : Nat → CV) (worlds : W2),
      PairedReadFrontierAt f result event env program MR Z entry prefixRecords output.state before regs worlds →
      ∃ nextRegs nextWorlds,∃ post : PairedReadFrontierAt f result event env program MR Z entry
        (prefixRecords++output.records.reverse) input after nextRegs nextWorlds,
        seqRun (pairSem isem) (output.code.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs worlds = some (.fall nextRegs nextWorlds) := by
  induction scanned with
  | nil input =>
    intro prefixRecords before after steps regs worlds prior
    cases steps
    exact ⟨regs,worlds,by simpa only [List.reverse_nil,List.append_nil] using prior,rfl⟩
  | @cons i indices input scan tail head rest ih =>
    intro prefixRecords before after steps regs worlds prior
    have split : SourceSteps (IndexedSourceInst env program f event.ctx event.block)
        (indices.reverse++[i]) before after := by simpa only [List.reverse_cons] using steps
    obtain ⟨middle,front,last⟩ := source_steps_append_split split
    obtain ⟨middleRegs,middleWorlds,middleRelated,firstRun⟩ := ih
      (fun record member => localRuns record (List.mem_cons_of_mem _ member)) prefixRecords before middle front regs worlds prior
    cases last with
    | cons source done =>
      cases done
      obtain ⟨nextRegs,nextWorlds,post,lastRun⟩ := localRuns ⟨i,input,scan⟩ (List.mem_cons_self ..)
        (prefixRecords++tail.records.reverse) middle after source middleRegs middleWorlds middleRelated
      refine ⟨nextRegs,nextWorlds,?_,?_⟩
      · simpa only [List.reverse_cons,List.append_assoc] using post
      · simp only [Array.toList_append,List.map_append]
        exact seqRun_append_fall' (pairSem isem) firstRun lastRun

end Backend.Stock.Proof.Acquire810

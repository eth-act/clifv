import FV.Backend.Proof.StockAcquireProgramEntryPrefixFault

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Internal prefix composition stops at an actual retained record. It requires no future source outcome.
The relation can carry the general pending queue; empty groups and pure emitted chunks remain covered.
Local refinement obligations must be proved internally before a final driver theorem uses this interface. -/
theorem scan_machine_prefix_at_record {S W : Type} {exec : Nat → State → Except String Scan}
    {source : Nat → S → S → Prop} {sem : ISem CV W} {aliases : Array (Option Nat)}
    {rel : State → S → (Nat → CV) → W → Prop}
    {indices : List Nat} {input : State} {output : BlockScan} {selected : ScanRecord}
    (scanned : ScansSpec exec indices input output) (member : selected ∈ output.records)
    (localRuns : ∀ record ∈ output.records,ScanFallRefines source sem aliases rel record) :
    ∃ (sourceBefore sourceAfter : List Nat) (codeBefore codeAfter : List MInst),
      indices.reverse = sourceBefore++selected.inst::sourceAfter ∧
      output.code.toList.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
        codeBefore++selected.output.emitted.toList.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))++codeAfter ∧
      ∀ (before after : S),SourceSteps source sourceBefore before after → ∀ (regs : Nat → CV) (world : W),
        rel output.state before regs world →
        ∃ nextRegs nextWorld,seqRun sem codeBefore regs world = some (.fall nextRegs nextWorld) ∧
          rel selected.output.state after nextRegs nextWorld := by
  induction scanned with
  | nil input => cases member
  | @cons i indices input scan tail head rest ih =>
    rcases List.mem_cons.mp member with first | later
    · subst selected
      refine ⟨indices.reverse,[],tail.code.toList.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),[],?_,?_,?_⟩
      · simp only [List.reverse_cons,List.append_nil,List.cons_append,List.nil_append]
      · simp only [Array.toList_append,List.map_append,List.append_nil]
      · intro before after steps regs world related
        exact rest.fall_refines (fun record present => localRuns record (List.mem_cons_of_mem _ present))
          before after steps regs world related
    · obtain ⟨sourceBefore,sourceAfter,codeBefore,codeAfter,sourceParts,codeParts,prefixRun⟩ :=
        ih later (fun record present => localRuns record (List.mem_cons_of_mem _ present))
      refine ⟨sourceBefore,sourceAfter++[i],codeBefore,
        codeAfter++scan.emitted.toList.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),?_,?_,prefixRun⟩
      · simp only [List.reverse_cons,sourceParts,List.append_assoc,List.cons_append]
      · simp only [Array.toList_append,List.map_append,codeParts,List.append_assoc]

/-- The actual Stock scan supplies the prefix structure without a replay/checker assumption. -/
theorem stock_lower_event_machine_prefix_at_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {selected : ScanRecord} (member : selected ∈ event.output.records)
    {S W : Type} {source : Nat → S → S → Prop} {sem : ISem CV W}
    {rel : State → S → (Nat → CV) → W → Prop}
    (localRuns : ∀ record ∈ event.output.records,ScanFallRefines source sem result.final.alias rel record) :
    ∃ (sourceBefore sourceAfter : List Nat) (codeBefore codeAfter : List MInst),
      event.indices.reverse = sourceBefore++selected.inst::sourceAfter ∧
      event.output.code.toList.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
        codeBefore++selected.output.emitted.toList.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))++codeAfter ∧
      ∀ (before after : S),SourceSteps source sourceBefore before after → ∀ (regs : Nat → CV) (world : W),
        rel event.output.state before regs world →
        ∃ nextRegs nextWorld,seqRun sem codeBefore regs world = some (.fall nextRegs nextWorld) ∧
          rel selected.output.state after nextRegs nextWorld := by
  exact scan_machine_prefix_at_record (runScans_spec (stock_lower_event_scan_run run events)) member localRuns

end Backend.Stock.Proof.Acquire810

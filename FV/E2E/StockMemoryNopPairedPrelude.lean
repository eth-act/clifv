import FV.Backend.Proof.StockMaskBlockRecords
import FV.E2E.StockMemoryOmittedPairedScan

/-! UNVALIDATED next-batch source. The frozen production packet excludes this file.
Derive the entry NOP body from actual omitted records. Memory instructions in
other original blocks do not add a global format restriction. -/
namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- Use the exact body split from a jump specification. Original NOP syntax
derives its paired execution without a global source-format restriction. -/
theorem stock_nop_paired_body_of_split {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ w →
          ∃ ρ' w',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' w' := by
  have each : ∀ record ∈ body.records,ScanFallRefines
      (IndexedSourceInst env cp f event.ctx event.block) (pairSem (csem Γ.F fc X)) result.final.alias
      (PairedScanRel f result event.ctx event.block Γ c D) record := by
    intro record member
    obtain ⟨j,stm,statement,current⟩ := split.positions record member
    obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events
      split member statement current (nops stm (List.mem_of_getElem? statement))
    have executed := records_execute split.scanned record member
    exact stock_lower_omitted_paired_scan run scope dominated events
      (split.retained record member) split.block statement current executed recorded omitted
  intro s s' steps ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [split.state] using held

/-- Original NOP syntax derives paired execution of the actual body. -/
theorem stock_nop_paired_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ w →
          ∃ ρ' w',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' w' := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := Option.some.inj (split.block.symm.trans block)
  subst original
  exact ⟨term,body,split,stock_nop_paired_body_of_split run scope dominated events block nops split⟩

end E2E.StockMemory

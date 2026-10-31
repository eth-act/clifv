import FV.Backend.Proof.StockMemoryRetainedReturnSpec
import FV.E2E.StockMemoryOmittedPairedScan
import FV.E2E.StockMemoryPairedScan

/-! UNVALIDATED next-batch body composition; excluded from frozen author HEAD. -/
namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

/-- Original load/NOP/return body syntax derives the complete paired body execution.
Both semantic consumers share the same retained-body derivation; neither a
record nor selected root, code, alias or read-permission certificate is an input. -/
theorem stock_nop_load_return_paired_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {loadIndex x z : Nat} {flags : Clif.MemFlags}
    (statement : b.body[loadIndex]? = some ⟨[z],.load .load .i32 flags x 0⟩)
    (shape : ∀ j stm,b.body[j]? = some stm → j = loadIndex ∨ stm.inst = .nop)
    (ret : b.term = .ret [z])
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (parameter : x ∈ pb.params.map (·.1))
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n b,Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ q,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ q →
          ∃ ρ' q',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
              some (.fall ρ' q') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' q' := by
  obtain ⟨spec⟩ := stock_retained_load_return_spec run scope dominated events block statement ret parameterBlock parameter
  have normal := stock_lower_load_paired_scan run scope dominated events spec.records block statement spec.current
    spec.source spec.clif spec.results rfl spec.mapped spec.parameter spec.pointer spec.recorded spec.emitted
    slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  refine ⟨spec.term,spec.body,spec.split,?_⟩
  have each : ∀ r ∈ spec.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      (pairSem (csem Γ.F fc X)) result.final.alias (PairedScanRel f result event.ctx event.block Γ c D) r := by
    intro r present
    rcases spec.nop_records run scope events shape r present with same | ⟨step,recorded,omitted⟩
    · subst r
      exact normal
    · obtain ⟨j,stm,sourceStmt,current⟩ := spec.split.positions r present
      have executed := records_execute spec.split.scanned r present
      exact stock_lower_omitted_paired_scan run scope dominated events
        (spec.split.retained r present) spec.split.block sourceStmt current executed recorded omitted
  intro s s' steps ρ q held
  apply spec.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [spec.split.state] using held

end E2E.StockMemory

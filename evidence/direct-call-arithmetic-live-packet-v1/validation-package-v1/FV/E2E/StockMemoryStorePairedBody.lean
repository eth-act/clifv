import FV.Backend.Proof.StockMemoryStoreReturnSpec
import FV.E2E.StockMemoryStorePairedScan

namespace E2E.StockMemory.StoreRoots
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original store/return body syntax derives the complete paired body execution.
Both semantic consumers share the same retained-body derivation; neither a
record nor selected root, code, alias or read-permission certificate is an input. -/
theorem stock_single_store_return_paired_body (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {value pointer : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩]) (ret : b.term = .ret [])
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
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
  obtain ⟨spec⟩ := stock_single_store_return_spec kind ty run scope dominated formats events block
    singleton ret pointerBlock parameter valueBlock valueParameter width
  have statement : b.body[0]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by simp [singleton]
  have normal := stock_lower_integer_store_paired_scan kind ty run scope dominated events spec.records
    block statement spec.current spec.source spec.clif spec.typed spec.parameter spec.pointerMapped
    spec.valueMapped spec.recorded spec.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  refine ⟨spec.term,spec.body,spec.split,?_⟩
  have each : ∀ r ∈ spec.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      (pairSem (csem Γ.F fc X)) result.final.alias (PairedScanRel f result event.ctx event.block Γ c D) r := by
    intro r present
    have same : r = spec.record := by simpa only [spec.bodyRecords,List.mem_singleton] using present
    subst r
    exact normal
  intro s s' steps ρ q held
  apply spec.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [spec.split.state] using held

end E2E.StockMemory.StoreRoots

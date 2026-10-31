import FV.Backend.Proof.StockMemoryStoreScanRefines
import FV.Backend.Proof.StockMemoryStoreReturnSpec

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original singleton store/return syntax derives the complete guarded body
proof, including retention, actual selection, value/pointer mappings and final
aliases. The pointer can be inherited from a different original source block.
No retained-record, selected-rule or emitted-code certificate is a premise. -/
theorem stock_single_store_return_body (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
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
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : StoreRefines F sb isem)
    (memoryOk : MemRelOk F sb syms f MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨spec⟩ := stock_single_store_return_spec kind ty run scope dominated formats events block
    singleton ret pointerBlock parameter valueBlock valueParameter width
  have statement : b.body[0]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by simp [singleton]
  have normal := stock_lower_integer_store_scan_fall_refines kind ty run scope dominated events spec.records
    block statement spec.current spec.source spec.clif spec.typed spec.parameter spec.pointerMapped
    spec.valueMapped spec.recorded spec.emitted stable memorySem memoryOk (env := env) (cp := cp)
  refine ⟨spec.term,spec.body,spec.split,?_⟩
  have each : ∀ r ∈ spec.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r present
    have same : r = spec.record := by simpa only [spec.bodyRecords,List.mem_singleton] using present
    subst r
    exact normal
  intro s s' steps ρ w held
  apply spec.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [spec.split.state] using held

end Backend.Stock.Memory.StoreRoots

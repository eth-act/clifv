import FV.Backend.Proof.StockMemoryLoadStoreReturnSpec
import FV.E2E.StockMemoryIntegerPairedScan
import FV.E2E.StockMemoryStorePairedScan

namespace E2E.StockMemory.LoadStore
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.LoadStore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Both actual records compose in paired worlds with their updated memory relation. -/
theorem load_store_return_paired_body (width : Backend.Stock.Memory.IntegerRoots.Width) (kind : Backend.Stock.Memory.StoreRoots.Kind) (ty : Clif.Ty)
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {loadPointer storePointer value z : Nat} {loadFlags storeFlags : Clif.MemFlags}
    (shape : b.body = [⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩,
      ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩]) (ret : b.term = .ret [z])
    {li si vi : Nat} {lb sb vb : Clif.Block} {valueTy : Clif.Ty}
    (loadBlock : f.blocks[li]? = some lb) (loadParameter : loadPointer ∈ lb.params.map (·.1))
    (storeBlock : f.blocks[si]? = some sb) (storeParameter : storePointer ∈ sb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ q,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ q →
          ∃ ρ' q',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
              some (.fall ρ' q') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' q' := by
  obtain ⟨spec⟩ := stock_mixed_load_store_return_spec width kind ty run scope dominated events block shape ret
    loadBlock loadParameter storeBlock storeParameter valueBlock valueParameter storeWidth
  let load := spec.load
  let store := spec.store
  have loadStatement : b.body[0]? = some ⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩ := by simp [shape]
  have storeStatement : b.body[1]? = some ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩ := by simp [shape]
  have loadRefines := IntegerRoots.stock_lower_integer_load_paired_scan width run scope dominated
    events load.records block loadStatement load.current load.source load.clif load.results rfl load.mapped
    load.parameter load.pointer load.recorded load.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have storeRefines := StoreRoots.stock_lower_integer_store_paired_scan kind ty run scope dominated
    events store.records block storeStatement store.current store.source store.clif store.typed store.parameter
    store.pointerMapped store.valueMapped store.recorded store.emitted slot symbols tls
    (env := env) (cp := cp) (c := c) (D := D)
  have each : ∀ record ∈ load.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      (pairSem (csem Γ.F fc X)) result.final.alias (PairedScanRel f result event.ctx event.block Γ c D) record := by
    intro record member
    rcases spec.family record member with rfl | rfl
    · exact loadRefines
    · exact storeRefines
  refine ⟨load.term,load.body,load.split,?_⟩
  intro s s' steps ρ q held
  apply load.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [load.split.state] using held

end E2E.StockMemory.LoadStore

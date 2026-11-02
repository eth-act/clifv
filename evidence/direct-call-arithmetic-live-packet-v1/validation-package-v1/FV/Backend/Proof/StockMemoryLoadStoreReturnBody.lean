import FV.Backend.Proof.StockMemoryLoadStoreReturnSpec
import FV.Backend.Proof.StockMemoryIntegerScanRefines
import FV.Backend.Proof.StockMemoryStoreScanRefines

namespace Backend.Stock.Memory.LoadStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original mixed load/store syntax derives both actual records and their guarded composition.
The machine relation carries the store's updated memory through the returned load value. -/
theorem load_store_return_body (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
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
    {F : BitVec 64 → Prop} {base : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F base syms isem)
    (memoryOk : MemRelOk F base syms f MR) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w' := by
  obtain ⟨spec⟩ := stock_mixed_load_store_return_spec width kind ty run scope dominated events block shape ret
    loadBlock loadParameter storeBlock storeParameter valueBlock valueParameter storeWidth
  let load := spec.load
  let store := spec.store
  have loadStatement : b.body[0]? = some ⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩ := by simp [shape]
  have storeStatement : b.body[1]? = some ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩ := by simp [shape]
  have loadRefines := IntegerRoots.stock_lower_integer_load_scan_fall_refines width run scope dominated
    events load.records block loadStatement load.current load.source load.clif load.results rfl load.mapped
    load.parameter load.pointer load.recorded load.emitted stable memorySem memoryOk (env := env) (cp := cp)
  have storeRefines := StoreRoots.stock_lower_integer_store_scan_fall_refines kind ty run scope dominated
    events store.records block storeStatement store.current store.source store.clif store.typed store.parameter
    store.pointerMapped store.valueMapped store.recorded store.emitted stable (store_refines_of_mem memorySem)
    memoryOk (env := env) (cp := cp)
  have each : ∀ record ∈ load.body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
    intro record member
    rcases spec.family record member with rfl | rfl
    · exact loadRefines
    · exact storeRefines
  refine ⟨load.term,load.body,load.split,?_⟩
  intro s s' steps ρ w held
  apply load.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [load.split.state] using held

end Backend.Stock.Memory.LoadStore

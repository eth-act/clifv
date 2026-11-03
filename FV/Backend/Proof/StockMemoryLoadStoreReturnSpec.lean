import FV.Backend.Proof.StockMemoryIntegerRetainedReturnSpec
import FV.Backend.Proof.StockMemoryMixedStoreRecordSpec

namespace Backend.Stock.Memory.LoadStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Both consumers use the same actual retained records and source positions. -/
structure ReturnSpec (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
    (f : Clif.Function) (result : Result) (event : BlockScanEvent) (b : Clif.Block)
    (loadPointer storePointer value z : Nat) (loadFlags storeFlags : Clif.MemFlags) where
  load : IntegerRoots.RetainedIntegerLoadReturnSpec width f result event b 0 loadPointer z loadFlags
  store : StoreRoots.RetainedStoreReturnSpec kind ty f result event b 1 value storePointer storeFlags
  sameRecords : store.body.records = load.body.records
  family : ∀ record ∈ load.body.records,record = load.record ∨ record = store.record

/-- Original source syntax derives the complete mixed retained-record contract. -/
theorem stock_mixed_load_store_return_spec (width : IntegerRoots.Width) (kind : StoreRoots.Kind) (ty : Clif.Ty)
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
    (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
    Nonempty (ReturnSpec width kind ty f result event b loadPointer storePointer value z loadFlags storeFlags) := by
  have loadStatement : b.body[0]? = some ⟨[z],.load .load width.sourceTy loadFlags loadPointer 0⟩ := by simp [shape]
  have storeStatement : b.body[1]? = some ⟨[],.store kind.sourceOp ty storeFlags value storePointer 0⟩ := by simp [shape]
  obtain ⟨load⟩ := IntegerRoots.stock_retained_integer_load_return_spec width run scope dominated
    events block loadStatement ret loadBlock loadParameter
  obtain ⟨store⟩ := StoreRoots.stock_mixed_store_record_spec kind ty run scope dominated
    events block storeStatement storeBlock storeParameter valueBlock valueParameter storeWidth
  have sameRecords : store.body.records = load.body.records :=
    (List.cons.inj (store.split.records.symm.trans load.split.records)).2
  have storeMember : store.record ∈ load.body.records := by rw [← sameRecords]; exact store.bodyMember
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨⟨load,store,sameRecords,?_⟩⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := load.split.positions record member
  have bound := lt_of_getElem? statement
  have positions : j = 0 ∨ j = 1 := by rw [shape] at bound; simp only [List.length_cons,List.length_nil] at bound; omega
  rcases positions with rfl | rfl
  · exact Or.inl (load.split.scanned.record_unique unique member load.bodyMember (current.trans load.current.symm))
  · exact Or.inr (load.split.scanned.record_unique unique member storeMember (current.trans store.current.symm))

end Backend.Stock.Memory.LoadStore

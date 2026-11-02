import FV.Backend.Proof.StockMemorySretCopyBodySpec
import FV.E2E.StockMemoryOffsetEightPairedScan
import FV.E2E.StockMemoryIntegerPairedScan
import FV.E2E.StockMemoryOmittedPairedScan
import FV.E2E.StockMemoryPairedScan
import FV.E2E.StockMemoryStorePairedScan
import FV.E2E.StockMemoryOffsetEightStorePairedScan

namespace E2E.StockMemory.SretCopy
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.SretCopy
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

/-- Original source syntax derives the complete guarded copy body with updated memory. -/
theorem captured_sret_copy_paired_body {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {i0 i8 j0 j8 base destination low high : Nat} {lf0 lf8 sf0 sf8 : Clif.MemFlags}
    (loadLow : b.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩)
    (loadHigh : b.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩)
    (storeLow : b.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩)
    (storeHigh : b.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩)
    (lowEarlier : i0 < j0) (highEarlier : i8 < j8)
    (shape : ∀ j stm,b.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop)
    {pi : Nat} {pb : Clif.Block} (parameterBlock : f.blocks[pi]? = some pb)
    (baseParameter : base ∈ pb.params.map (·.1))
    (destinationParameter : destination ∈ pb.params.map (·.1))
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ w →
          ∃ ρ' w',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
              some (.fall ρ' w') ∧
            PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' w' := by
  obtain ⟨spec⟩ := captured_sret_copy_body_spec run scope dominated events block
    loadLow loadHigh storeLow storeHigh lowEarlier highEarlier shape parameterBlock baseParameter destinationParameter
  have lowLoad := IntegerRoots.stock_lower_integer_load_paired_scan .w64 run scope dominated
    events (spec.split.retained spec.loadLow.record spec.loadLow.member) block loadLow spec.loadLow.current
    spec.loadLow.source spec.loadLow.clif spec.loadLow.results rfl spec.lowMapped spec.baseParameter spec.baseMapped
    spec.loadLow.recorded spec.loadLow.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have highLoad := IntegerRoots.stock_lower_integer_load_eight_paired_scan .w64 run scope dominated
    events (spec.split.retained spec.loadHigh.record spec.loadHigh.member) block loadHigh spec.loadHigh.current
    spec.loadHigh.source spec.loadHigh.clif spec.loadHigh.results rfl spec.highMapped spec.baseParameter spec.baseMapped
    spec.loadHigh.recorded spec.loadHigh.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have lowStore := StoreRoots.stock_lower_integer_store_paired_scan .plain64 .i64 run scope dominated
    events (spec.split.retained spec.storeLow.record spec.storeLow.member) block storeLow spec.storeLow.current
    spec.storeLow.source spec.storeLow.clif (fun _ => spec.lowType) spec.destinationParameter spec.destinationMapped spec.lowMapped
    spec.storeLow.recorded spec.storeLow.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have highStore := StoreRoots.stock_lower_integer_store_eight_paired_scan .plain64 .i64 run scope dominated
    events (spec.split.retained spec.storeHigh.record spec.storeHigh.member) block storeHigh spec.storeHigh.current
    spec.storeHigh.source spec.storeHigh.clif (fun _ => spec.highType) spec.destinationParameter spec.destinationMapped spec.highMapped
    spec.storeHigh.recorded spec.storeHigh.emitted slot symbols tls (env := env) (cp := cp) (c := c) (D := D)
  have each : ∀ record ∈ spec.body.records,ScanFallRefines
      (IndexedSourceInst env cp f event.ctx event.block) (pairSem (csem Γ.F fc X)) result.final.alias
      (PairedScanRel f result event.ctx event.block Γ c D) record := by
    intro record member
    rcases spec.family record member with rfl | rfl | rfl | rfl | ⟨step,recorded,omitted⟩
    · exact lowLoad
    · exact highLoad
    · exact lowStore
    · exact highStore
    · obtain ⟨j,stm,statement,current⟩ := spec.split.positions record member
      have actual := records_execute spec.split.scanned record member
      exact stock_lower_omitted_paired_scan run scope dominated events
        (spec.split.retained record member) spec.split.block statement current actual recorded omitted
  refine ⟨spec.term,spec.body,spec.split,?_⟩
  intro s s' steps ρ w held
  apply spec.split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using steps
  · simpa only [spec.split.state] using held

end E2E.StockMemory.SretCopy

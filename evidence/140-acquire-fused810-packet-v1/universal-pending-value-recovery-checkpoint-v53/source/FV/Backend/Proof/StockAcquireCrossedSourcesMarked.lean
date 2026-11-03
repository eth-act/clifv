import FV.Backend.Proof.StockAcquireRecordOutputMarkedCut

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every crossed source effect is actually marked by the original scan, not merely classified as a read. -/
theorem stock_lower_record_crossed_sources_marked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {final : Nat} (color : record.output.state.color = some final) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      record.input.entryColor = (sourceMetadata original ranges).entryColor ∧
      ∀ producer,some producer ∈ sourceColorEvents original ranges → producer < record.inst →
        final ≤ (sourceMetadata original ranges).entryColor[producer]! →
        record.output.state.sunk[producer]! = true := by
  obtain ⟨original,ranges,initial,earlier,scan,suffix,groups,built,prefixRun,boundary,parts,indexParts,
    frontiers,exactSunk,covered,marked⟩ := stock_lower_record_output_marked_read_queue_cut run scope events records
  obtain ⟨other,otherRanges,otherInitial,bi,block,otherBuilt,blockAt,termEq,indicesEq,
    terminalSource,notSunk,entryColors,metadata⟩ := stock_lower_event_cut_source run scope events
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨rfl,rfl,rfl⟩
  refine ⟨original,ranges,initial,built,metadata record records,?_⟩
  intro producer source before lower
  have upper := stock_lower_record_prefix_cut_above run scope events otherBuilt indexParts source before
  exact marked producer (covered.1 final color producer source lower upper)

end Backend.Stock.Proof.Acquire810

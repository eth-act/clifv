import FV.Backend.Proof.StockAcquireBlockColorInterval

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained output colors stay inside their original source block's event interval. -/
theorem stock_lower_record_output_block_colors {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (bi : Nat) (block : Clif.Block),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[bi]? = some block ∧
      event.termInst = blockStart f bi+block.body.length ∧
      ∀ color,record.output.state.color = some color → sourceBlockBoundary f ranges bi < color ∧
        color ≤ (sourceMetadata original ranges).entryColor[blockStart f bi+block.body.length]! := by
  obtain ⟨original,ranges,initial,earlier,suffix,built,parts,gap⟩ :=
    stock_lower_record_output_source_color_gap run scope events records
  obtain ⟨other,otherRanges,otherInitial,bi,block,otherBuilt,blockAt,termEq,cutAbove⟩ :=
    stock_lower_prefix_cut_above_boundary run scope events parts (by simp)
  have equal := Except.ok.inj (built.symm.trans otherBuilt)
  have ctxEq : original = other := congrArg Prod.fst equal
  have rangesEq : ranges = otherRanges := congrArg (fun pair => pair.2.1) equal
  rw [← ctxEq,← rangesEq] at cutAbove
  obtain ⟨capCtx,capRanges,capInitial,capBuilt,capped⟩ := stock_lower_record_output_color_upper run scope events records
  have capEqual := Except.ok.inj (built.symm.trans capBuilt)
  have capCtxEq : original = capCtx := congrArg Prod.fst capEqual
  have capRangesEq : ranges = capRanges := congrArg (fun pair => pair.2.1) capEqual
  rw [← capCtxEq,← capRangesEq,termEq] at capped
  refine ⟨original,ranges,initial,bi,block,built,blockAt,termEq,?_⟩
  intro color actual
  exact ⟨gap.above_block_boundary built blockAt actual cutAbove,capped color actual⟩

/-- A source event whose color lies inside a block interval belongs to that actual block chunk. -/
theorem source_event_same_block_of_color {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    {bi : Nat} {block : Clif.Block} (blockAt : f.blocks[bi]? = some block) {producer : Nat}
    (source : some producer ∈ sourceColorEvents ctx ranges)
    (lower : sourceBlockBoundary f ranges bi < (sourceMetadata ctx ranges).entryColor[producer]!)
    (upper : (sourceMetadata ctx ranges).entryColor[producer]! ≤
      (sourceMetadata ctx ranges).entryColor[blockStart f bi+block.body.length]!) :
    some producer ∈ blockColorEvents ranges (block,bi) := by
  have lookup := source_color_event_lookup built producer source
  have rangesAt := (ctxSpec_of built).ranges bi block blockAt
  have rangesValue : ranges[bi]! = (blockStart f bi,blockStart f bi+block.body.length+1) := by
    simp only [getElem!_def,rangesAt]
  have chunkLength : (blockColorEvents ranges (block,bi)).length =
      (bodyColorEvents (blockStart f bi) block.body.zipIdx).length+2 := by
    simp only [blockColorEvents,rangesValue,List.length_cons,List.length_append,List.length_nil]
  have inside : (sourceMetadata ctx ranges).entryColor[producer]! - sourceBlockBoundary f ranges bi <
      (blockColorEvents ranges (block,bi)).length := by
    rw [source_block_terminal_color built blockAt] at upper
    rw [chunkLength]
    omega
  have afterPrefix : ((f.blocks.zipIdx.take bi).flatMap (blockColorEvents ranges)).length ≤
      (sourceMetadata ctx ranges).entryColor[producer]! := by exact Nat.le_of_lt lower
  rw [source_block_event_split built blockAt,List.append_assoc,List.getElem?_append_right afterPrefix] at lookup
  change (blockColorEvents ranges (block,bi) ++ ((f.blocks.zipIdx.drop (bi+1)).flatMap (blockColorEvents ranges)))[(sourceMetadata ctx ranges).entryColor[producer]! - sourceBlockBoundary f ranges bi]? = some (some producer) at lookup
  rw [List.getElem?_append_left inside] at lookup
  exact List.mem_of_getElem? lookup

end Backend.Stock.Proof.Acquire810

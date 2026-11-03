import FV.Backend.Proof.StockAcquireScanStateBlockCap

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every real sink group belongs to its own original block, derived from actual color boundaries.
The complete group remains general. Inherited marks and all old source conditions remain unchanged. -/
theorem stock_lower_record_sink_block_owner {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {pending : List Nat} (frontier : ExecutedRecordFrontier f event.ctx record pending) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (block : Clif.Block),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ f.blocks[event.block]? = some block ∧
      ∀ producer ∈ pending,some producer ∈ blockColorEvents ranges (block,event.block) := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,blockBounds⟩ :=
    stock_lower_record_output_block_colors run scope events records
  obtain ⟨actualBlock,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have blockIndex := source_block_terminal_unique blockAt split.block (termEq.symm.trans split.termIndex)
  subst bi
  obtain ⟨other,otherRanges,otherInitial,otherBuilt,recordMeta,capped⟩ :=
    stock_lower_record_scan_state_color_cap run scope events records
  have equal := Except.ok.inj (otherBuilt.symm.trans built)
  have ctxEq := congrArg Prod.fst equal
  have rangesEq := congrArg (fun pair => pair.2.1) equal
  dsimp only at ctxEq rangesEq
  rw [ctxEq,rangesEq] at recordMeta capped
  refine ⟨original,ranges,initial,block,built,blockAt,?_⟩
  intro producer member
  rcases frontier.1.2.2 with ⟨step,recorded,emitted,marks⟩ | ⟨empty,same⟩
  · have nonempty : pending ≠ [] := by intro empty;rw [empty] at member;cases member
    have trace := marks.forget
    obtain ⟨final,color⟩ := trace.nonempty_color nonempty
    have bounds := trace.member_color_bounds color producer member
    have start := trace.color_distance color
    have initialBound := capped (final+pending.length) start
    have metadata : (scanState record.input record.inst).entryColor = (sourceMetadata original ranges).entryColor :=
      (scanState_entry_colors record.input record.inst).trans recordMeta
    have source := trace.source_members built metadata producer member
    rw [metadata] at bounds
    have actualBounds := blockBounds final color
    apply source_event_same_block_of_color built blockAt source
    · omega
    · rw [← termEq]
      omega
  · rw [empty] at member
    cases member

end Backend.Stock.Proof.Acquire810

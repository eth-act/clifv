import FV.Backend.Proof.StockAcquireActualPendingColorOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A nonempty real sink trace derives its final execution color internally. -/
theorem PendingSinks.nonempty_color {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) (nonempty : pending ≠ []) :
    ∃ final,after.color = some final := by
  induction trace with
  | nil => exact False.elim (nonempty rfl)
  | @sink before middle after producer rest actual tail ih =>
    have color : middle.color = some before.entryColor[producer]! := by rw [(sink_accepted actual).2.2.2.2]
    obtain ⟨final,finished,bound⟩ := tail.color_some color
    exact ⟨final,finished⟩
  | frame entries unchanged tail ih => exact ih nonempty

/-- Every actual retained group's complete pending list has strict reverse source order. -/
theorem stock_lower_frontier_pending_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {pending : List Nat} (frontier : RecordFrontier f event.ctx record pending) :
    pending.Pairwise (fun first second => second < first) := by
  rcases frontier.2.2 with ⟨step,recorded,emitted,trace⟩ | ⟨empty,same⟩
  · by_cases empty : pending = []
    · rw [empty];exact .nil
    · obtain ⟨final,color⟩ := trace.forget.nonempty_color empty
      obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events records
      have metadata : (scanState record.input record.inst).entryColor = (sourceMetadata original ranges).entryColor :=
        (scanState_entry_colors _ _).trans (table.trans (sourceMetadata_color_events original ranges).symm)
      exact trace.forget.source_order built metadata color
  · rw [empty];exact .nil

/-- Actual ordered records put every later pending producer strictly before every earlier pending producer. -/
theorem stock_lower_frontier_pending_cross_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {first second : ScanRecord}
    (events : event ∈ result.blockScans.toList) (firstMem : first ∈ event.output.records)
    (secondMem : second ∈ event.output.records)
    (ordered : ∀ color,first.output.state.color = some color → ∀ step,
      second.output.step = some step → step.decision = .emitted →
      ColorUpperBound color (scanState second.input second.inst))
    {left right : List Nat} (firstFrontier : RecordFrontier f event.ctx first left)
    (secondFrontier : RecordFrontier f event.ctx second right) {a b : Nat}
    (firstMember : a ∈ left) (secondMember : b ∈ right) : b < a := by
  rcases firstFrontier.2.2 with ⟨firstStep,firstRecorded,firstEmitted,firstTrace⟩ | ⟨empty,same⟩
  · rcases secondFrontier.2.2 with ⟨secondStep,secondRecorded,secondEmitted,secondTrace⟩ | ⟨empty,same⟩
    · have leftNonempty : left ≠ [] := by intro empty;rw [empty] at firstMember;cases firstMember
      have rightNonempty : right ≠ [] := by intro empty;rw [empty] at secondMember;cases secondMember
      obtain ⟨firstColor,firstSome⟩ := firstTrace.forget.nonempty_color leftNonempty
      obtain ⟨secondColor,secondSome⟩ := secondTrace.forget.nonempty_color rightNonempty
      have firstBounds := firstTrace.forget.member_color_bounds firstSome a firstMember
      have secondBounds := secondTrace.forget.member_color_bounds secondSome b secondMember
      have secondStart := secondTrace.forget.color_distance secondSome
      have cap := ordered firstColor firstSome secondStep secondRecorded secondEmitted _ secondStart
      rw [scanState_entry_colors] at firstBounds secondBounds
      obtain ⟨original,ranges,initial,built,func,table⟩ := stock_lower_record_color_events run events firstMem
      have firstMetadata : first.input.entryColor = (sourceMetadata original ranges).entryColor :=
        table.trans (sourceMetadata_color_events original ranges).symm
      have firstEntries := ((((stock_lower_zeroColorLe run).2 event events).2 first firstMem).1).1
      have secondEntries := ((((stock_lower_zeroColorLe run).2 event events).2 second secondMem).1).1
      have secondMetadata : second.input.entryColor = (sourceMetadata original ranges).entryColor :=
        secondEntries.trans (firstEntries.symm.trans firstMetadata)
      rw [firstMetadata] at firstBounds
      rw [secondMetadata] at secondBounds
      have less : (sourceMetadata original ranges).entryColor[b]! < (sourceMetadata original ranges).entryColor[a]! := by omega
      have firstScanned := (scanState_entry_colors first.input first.inst).trans firstMetadata
      have secondScanned := (scanState_entry_colors second.input second.inst).trans secondMetadata
      have firstSource := firstTrace.forget.source_members built firstScanned a firstMember
      have secondSource := secondTrace.forget.source_members built secondScanned b secondMember
      exact source_color_order_reflects_slots built b a secondSource firstSource less
    · rw [empty] at secondMember;cases secondMember
  · rw [empty] at firstMember;cases firstMember

end Backend.Stock.Proof.Acquire810

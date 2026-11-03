import FV.Backend.Proof.StockAcquireScanColorFrame
import FV.Backend.Proof.StockAcquireScanIndexOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Actual scan specifications supply the precise interpreter call of every retained record. -/
theorem ScansSpec.record_run {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (spec : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction spec with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

private theorem covered_at_color {ctx original : Ctx} {ranges : Array (Nat × Nat)} {cut : Nat}
    {state : State} {queue : List Nat} (frames : ∀ producer ∈ queue,SourceReadFrame ctx producer)
    (color : state.color = some cut) : ReadQueueCut ctx original ranges cut state queue := by
  refine ⟨?_,frames⟩
  intro final same producer source lower upper
  have equal := Option.some.inj (color.symm.trans same)
  omega

/-- Actual scan decisions compose their derived queue and reference cut.
The sunk-only bound is an internal source-order obligation of the complete scan proof. -/
theorem stock_lower_record_read_queue_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {cut : Nat} {queue : List Nat} (covered : ReadQueueCut event.ctx original ranges cut record.input queue)
    (sunkCut : record.input.sunk[record.inst]! = true →
      referenceCut record.input.entryColor cut record.inst ≤ cut) :
    ∃ pending,RecordFrontier f event.ctx record pending ∧
      ReadQueueCut event.ctx original ranges (referenceCut record.input.entryColor cut record.inst)
        record.output.state (queue++pending) := by
  by_cases emitting : ∃ step,record.output.step = some step ∧ step.decision = .emitted
  · obtain ⟨step,recorded,emitted⟩ := emitting
    obtain ⟨pending,reads,exactSunk,frames⟩ := stock_lower_record_read_pending_marks run events records recorded emitted
    have scannedMeta := (scanState_entry_colors record.input record.inst).trans metadata
    have frontier : RecordFrontier f event.ctx record pending := by
      refine ⟨exactSunk,?_,Or.inl ⟨step,recorded,emitted,reads.forget⟩⟩
      intro producer member
      exact ⟨original,ranges,initial,built,reads.forget.forget.source_members built scannedMeta producer member⟩
    refine ⟨pending,frontier,?_⟩
    by_cases zero : record.input.entryColor[record.inst]! = 0
    · have normalized := covered.of_color_eq (scanState_color_zero record.input record.inst zero)
      have after := ReadQueueCut.append_execution built scannedMeta normalized reads
      simpa only [referenceCut,zero,ite_true] using after
    · have after := ReadQueueCut.reset_execution built scannedMeta covered
        (scanState_color_positive record.input record.inst zero) reads
      simpa only [referenceCut,zero,ite_false] using after
  · obtain ⟨pending,frontier⟩ := stock_lower_record_frontier run events records
    have empty : pending = [] := by
      rcases frontier.2.2 with ⟨step,recorded,emitted,marks⟩ | ⟨empty,unchanged⟩
      · exact False.elim (emitting ⟨step,recorded,emitted⟩)
      · exact empty
    have noneFrontier : RecordFrontier f event.ctx record [] := by simpa only [empty] using frontier
    refine ⟨[],noneFrontier,?_⟩
    have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) record records
    cases sunk : record.input.sunk[record.inst]! with
    | true =>
      have same := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block record.inst event.termInst event.isBranch record.input sunk))
      have colorEq := congrArg (fun scan : Scan => scan.state.color) same
      have after := (covered.shrink (sunkCut sunk)).of_color_eq colorEq
      simpa only [List.append_nil] using after
    | false =>
      have colorEq := scan_no_emission_color sunk actual (fun step recorded emitted => emitting ⟨step,recorded,emitted⟩)
      by_cases zero : record.input.entryColor[record.inst]! = 0
      · have after := covered.of_color_eq (colorEq.trans (scanState_color_zero record.input record.inst zero))
        simpa only [referenceCut,zero,ite_true,List.append_nil] using after
      · have after : ReadQueueCut event.ctx original ranges record.input.entryColor[record.inst]! record.output.state queue :=
          covered_at_color covered.2 (colorEq.trans (scanState_color_positive record.input record.inst zero))
        simpa only [referenceCut,zero,ite_false,List.append_nil] using after

end Backend.Stock.Proof.Acquire810

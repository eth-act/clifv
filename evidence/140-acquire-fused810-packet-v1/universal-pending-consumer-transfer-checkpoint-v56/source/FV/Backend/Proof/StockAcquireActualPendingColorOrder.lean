import FV.Backend.Proof.StockAcquireScanPendingColorOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every pair of real retained outputs has the execution-color order of the original reverse scan. -/
theorem ScansSpec.record_pending_colors_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records)
    (reverse : indices.Pairwise (fun first second => second < first)) :
    output.records.Pairwise (fun first second => ∀ color,first.output.state.color = some color →
      ∀ (step : Step),second.output.step = some step → step.decision = .emitted →
      ColorUpperBound color (scanState second.input second.inst)) := by
  induction spec with
  | nil => exact .nil
  | @cons inst indices before scan tail head rest ih =>
    let current : ScanRecord := ⟨inst,before,scan⟩
    have currentMem : current ∈ event.output.records := kept current (List.mem_cons_self ..)
    have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records :=
      fun retained member => kept retained (List.mem_cons_of_mem _ member)
    have tailLower : ∀ target ∈ indices,target < current.inst :=
      fun target member => (List.pairwise_cons.mp reverse).1 target member
    apply List.pairwise_cons.mpr
    constructor
    · intro later member color actual step recorded emitted
      have bounded := ScansSpec.emitted_colors_after_record run scope events rest current currentMem tailKept rfl
        tailLower (List.pairwise_cons.mp reverse).2 color actual later member step recorded emitted
      exact bounded
    · exact ih tailKept (List.pairwise_cons.mp reverse).2

/-- Whole successful Stock lowering derives the complete retained-record color order internally. -/
theorem stock_lower_event_record_pending_colors_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    event.output.records.Pairwise (fun first second => ∀ color,first.output.state.color = some color →
      ∀ (step : Step),second.output.step = some step → step.decision = .emitted →
      ColorUpperBound color (scanState second.input second.inst)) :=
  ScansSpec.record_pending_colors_order run scope events (runScans_spec (stock_lower_event_scan_run run events))
    (fun record member => member) (stock_lower_event_indices_reverse run scope events)

end Backend.Stock.Proof.Acquire810

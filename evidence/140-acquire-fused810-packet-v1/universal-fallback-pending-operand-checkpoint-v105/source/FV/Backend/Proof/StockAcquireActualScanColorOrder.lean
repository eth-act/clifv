import FV.Backend.Proof.StockAcquireScanColorSome

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual remaining scan stays below its preceding record's execution color. -/
theorem ScansSpec.colors_after_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output) :
    ∀ (previous : ScanRecord),previous ∈ event.output.records →
      (∀ record ∈ output.records,record ∈ event.output.records) → before = previous.output.state →
      (∀ inst ∈ indices,inst < previous.inst) → indices.Pairwise (fun first second => second < first) →
      ∀ color,previous.output.state.color = some color → ∀ record ∈ output.records,
        ∃ final,record.output.state.color = some final ∧ final ≤ color := by
  induction spec with
  | nil input => intro previous present kept following lower reverse color initial record member;cases member
  | @cons inst indices before scan tail head rest ih =>
    intro previous present kept following lower reverse color initial record member
    let current : ScanRecord := ⟨inst,before,scan⟩
    have currentMem : current ∈ event.output.records := kept current (List.mem_cons_self ..)
    have currentBound := stock_lower_record_color_after_previous run scope events present currentMem following
      (lower inst (List.mem_cons_self ..)) initial
    have inputColor : current.input.color = some color := by
      change before.color = some color
      rw [following]
      exact initial
    obtain ⟨currentColor,currentSome⟩ := stock_lower_record_color_some run events currentMem inputColor
    have currentLe := currentBound currentColor currentSome
    rcases List.mem_cons.mp member with equal | later
    · subst record
      exact ⟨currentColor,currentSome,currentLe⟩
    · have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records :=
        fun retained member => kept retained (List.mem_cons_of_mem _ member)
      have tailLower : ∀ target ∈ indices,target < current.inst :=
        fun target member => (List.pairwise_cons.mp reverse).1 target member
      obtain ⟨final,finished,bound⟩ := ih current currentMem tailKept rfl tailLower
        (List.pairwise_cons.mp reverse).2 currentColor currentSome record later
      exact ⟨final,finished,Nat.le_trans bound currentLe⟩

/-- Every pair of real retained outputs has the execution-color order of the original reverse scan. -/
theorem ScansSpec.record_colors_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records)
    (reverse : indices.Pairwise (fun first second => second < first)) :
    output.records.Pairwise (fun first second => ∀ color,first.output.state.color = some color →
      ColorUpperBound color second.output.state) := by
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
    · intro later member color actual
      obtain ⟨final,finished,bound⟩ := ScansSpec.colors_after_record run scope events rest current currentMem tailKept rfl
        tailLower (List.pairwise_cons.mp reverse).2 color actual later member
      exact ColorUpperBound.at_color finished bound
    · exact ih tailKept (List.pairwise_cons.mp reverse).2

/-- Whole successful Stock lowering derives the complete retained-record color order internally. -/
theorem stock_lower_event_record_colors_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    event.output.records.Pairwise (fun first second => ∀ color,first.output.state.color = some color →
      ColorUpperBound color second.output.state) :=
  ScansSpec.record_colors_order run scope events (runScans_spec (stock_lower_event_scan_run run events))
    (fun record member => member) (stock_lower_event_indices_reverse run scope events)

end Backend.Stock.Proof.Acquire810

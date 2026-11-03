import FV.Backend.Proof.StockAcquireEmittedScanColorOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual remaining scan stays below its preceding record's execution color. -/
theorem ScansSpec.emitted_colors_after_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output) :
    ∀ (previous : ScanRecord),previous ∈ event.output.records →
      (∀ record ∈ output.records,record ∈ event.output.records) → before = previous.output.state →
      (∀ inst ∈ indices,inst < previous.inst) → indices.Pairwise (fun first second => second < first) →
      ∀ color,previous.output.state.color = some color → ∀ record ∈ output.records,
        ∀ (step : Step),record.output.step = some step → step.decision = .emitted →
          ColorUpperBound color (scanState record.input record.inst) := by
  induction spec with
  | nil input => intro previous present kept following lower reverse color initial record member step recorded emitted;cases member
  | @cons inst indices before scan tail head rest ih =>
    intro previous present kept following lower reverse color initial record member step recorded emitted
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
      exact stock_lower_emitted_scan_color_after_previous run scope events present currentMem following
        (lower inst (List.mem_cons_self ..)) initial recorded emitted
    · have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records :=
        fun retained member => kept retained (List.mem_cons_of_mem _ member)
      have tailLower : ∀ target ∈ indices,target < current.inst :=
        fun target member => (List.pairwise_cons.mp reverse).1 target member
      have bounded := ih current currentMem tailKept rfl tailLower
        (List.pairwise_cons.mp reverse).2 currentColor currentSome record later step recorded emitted
      intro final actual
      exact Nat.le_trans (bounded final actual) currentLe


end Backend.Stock.Proof.Acquire810

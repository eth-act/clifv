import FV.Backend.Proof.StockAcquireCrossedSourcesMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual crossed-effect marks prevent the next reverse-scan record from increasing the execution color. -/
theorem stock_lower_record_color_after_previous {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent} {first second : ScanRecord}
    (events : event ∈ result.blockScans.toList) (firstMem : first ∈ event.output.records)
    (secondMem : second ∈ event.output.records) (following : second.input = first.output.state)
    (before : second.inst < first.inst) {color : Nat} (firstColor : first.output.state.color = some color) :
    ColorUpperBound color second.output.state := by
  have inputColor : second.input.color = some color := by rw [following];exact firstColor
  have priorBound : ColorUpperBound color second.input := ColorUpperBound.at_color inputColor (Nat.le_refl _)
  have actual := ScansSpec.record_run (runScans_spec (stock_lower_event_scan_run run events)) second secondMem
  cases sunk : second.input.sunk[second.inst]! with
  | true =>
    have same := Except.ok.inj (actual.symm.trans (scan_sunk event.ctx event.block second.inst event.termInst event.isBranch second.input sunk))
    exact priorBound.of_color_eq (congrArg (fun scan : Scan => scan.state.color) same)
  | false =>
    have resetBound : ColorUpperBound color (scanState second.input second.inst) := by
      by_cases zero : second.input.entryColor[second.inst]! = 0
      · exact priorBound.of_color_eq (scanState_color_zero second.input second.inst zero)
      · obtain ⟨original,ranges,initial,built,firstMetadata,crossed⟩ :=
          stock_lower_record_crossed_sources_marked run scope events firstMem firstColor
        have firstEntries := ((((stock_lower_zeroColorLe run).2 event events).2 first firstMem).1).1
        have secondEntries := ((((stock_lower_zeroColorLe run).2 event events).2 second secondMem).1).1
        have metadata : second.input.entryColor = (sourceMetadata original ranges).entryColor :=
          secondEntries.trans (firstEntries.symm.trans firstMetadata)
        have positive : (sourceMetadata original ranges).entryColor[second.inst]! ≠ 0 := by rwa [metadata] at zero
        have source := source_color_positive_member original ranges second.inst positive
        have less : second.input.entryColor[second.inst]! < color := by
          apply Nat.lt_of_not_ge
          intro reverse
          have marked := crossed second.inst source before (by rwa [← metadata])
          rw [← following,sunk] at marked
          cases marked
        exact ColorUpperBound.at_color (scanState_color_positive second.input second.inst zero) (Nat.le_of_lt less)
    apply stock_lower_record_color_upper_bound run events secondMem ?_ resetBound
    intro marked
    rw [sunk] at marked
    cases marked

end Backend.Stock.Proof.Acquire810

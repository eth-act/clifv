module

public import FV.Backend.Proof.StockPrologueAllClass
public import FV.Backend.Proof.StockPrologueAllSource

@[expose] public section

set_option autoImplicit false
namespace Backend.Stock.Prologue.AllConfigurations
open D0

/-- Simultaneous successful actual lowering, source-shape/SSA validation and
complete source execution. All configurations, values and initial memories are
inhabited, including nonzero machine high bits and placement oracles. -/
theorem complete_source_and_lowering_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (word : BitVec (valueType c).width)
    (upper : Nat) (mem : Clif.Mem) :
    ∃ (vc : VCode) (fr : Clif.Frame) (entered : Clif.Mem),
      lower (Prologue.source name c runs) = .ok vc ∧
      Backend.Proof.Driver.lowerCheck (Prologue.source name c runs) vc = true ∧
      Clif.enterFunc (Prologue.source name c runs) [⟨valueType c, word⟩] mem = .ok (fr, entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [Prologue.source name c runs]} 4 ⟨fr, [], entered⟩ =
        .returned [⟨valueType c, word⟩] mem ∧
      (BitVec.ofNat 128 (upper * 2^(valueType c).width + word.toNat)).setWidth
        (valueType c).width = word := by
  have checked := eligible_checked_output (source_eligible name runs c)
  obtain ⟨fr, entered, he, hr, bits⟩ := Source.source_complete_witness name c runs word upper mem
  cases run : lower (Prologue.source name c runs) with
  | error e => simp [run, Except.map] at checked
  | ok vc =>
    have hc : Backend.Proof.Driver.lowerCheck (Prologue.source name c runs) vc = true := by
      simpa [run, Except.map] using checked
    exact ⟨vc, fr, entered, rfl, hc, he, hr, bits⟩

end Backend.Stock.Prologue.AllConfigurations

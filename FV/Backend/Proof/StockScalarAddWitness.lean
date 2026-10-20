import FV.Backend.Proof.StockScalarAddClass
import FV.Backend.Proof.StockScalarAddSource

set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0

/-- The selector/checker and complete source execution are simultaneously
inhabited for every pair of argument words and arbitrary initial memory. -/
theorem complete_lowering_source_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (u v : BitVec (valueType c).width) (mem : Clif.Mem) :
    ∃ (vc : VCode) (fr : Clif.Frame) (entered : Clif.Mem),
      lower (source name c runs) = .ok vc ∧
      Backend.Proof.Driver.lowerCheck (source name c runs) vc = true ∧
      Clif.enterFunc (source name c runs) [Source.argument c u,Source.argument c v] mem = .ok (fr,entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [source name c runs]} 2 ⟨fr,[],entered⟩ =
        .returned [Source.argument c (u+v)] mem := by
  have checked := eligible_checked_output (source_eligible name runs c)
  obtain ⟨fr,entered,he,hr⟩ := Source.complete_source_witness name c runs u v mem
  cases run : lower (source name c runs) with
  | error e => simp [run,Except.map] at checked
  | ok vc =>
    have hc : Backend.Proof.Driver.lowerCheck (source name c runs) vc = true := by
      simpa [run,Except.map] using checked
    exact ⟨vc,fr,entered,rfl,hc,he,hr⟩
end Backend.Stock.ScalarAdd

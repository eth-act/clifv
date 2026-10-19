import StockPipelineProvenanceProbe
import FV.Backend.Proof.StockD0PipelineWitness

namespace E2E.LinkCheck.ActualCodeProbe
open Backend

/-- Actual successful Stock output inhabits the callback-provenance theorem,
for every D0 configuration and allocator answer; no joint-rejection witness. -/
theorem actual_stock_witness (name : String) (c : Stock.D0.Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (r : Stock.Result) (a : Art),
      Stock.lower (Stock.D0.source name c runs) = .ok r ∧
      pipeTWithLowering Stock.D0.defaultLower id (Stock.D0.source name c runs)
        k base answer = .ok a ∧
      a.vc = Stock.D0.compact name r ∧
      Stock.D0.defaultLower (Stock.D0.source name c runs) = .ok a.vc ∧
      prepare a.vc = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp answer)) := by
  obtain ⟨r, plain, clean, run, selected, hp, hc, code, cleanCode⟩ :=
    Stock.D0.complete_pipeline_witness name c runs k base answer
  have actual : pipeTWithLowering Stock.D0.defaultLower id
      (Stock.D0.source name c runs) k base answer = .ok plain := hp
  have facts := pipeTWithLowering_spec actual
  exact ⟨r, plain, run, actual, code, facts.1, facts.2.1, facts.2.2.1⟩

#print axioms actual_stock_witness
end E2E.LinkCheck.ActualCodeProbe

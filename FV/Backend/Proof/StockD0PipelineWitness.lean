import FV.Backend.Proof.StockD0DispatchWitness
import FV.E2E.LinkScopeInput
import FV.E2E.DeadCleanupLinkScope
import FV.E2E.SpillDefined

namespace Backend.Stock.D0
open E2E E2E.LinkCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

private theorem source_input_scope (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) : fnScopeInB (source name c runs) = true := by
  cases c <;> d0_open_kernel_decide

/-- Complete actual production pipelines for every D0 configuration, arbitrary
names/run metadata/allocator answers and both cleanup modes. The artifacts carry
the actual normalized Stock result, not just an observationally equal fallback. -/
theorem complete_pipeline_witness (name : String) (c : Configuration)
    (runs : List Clif.RunCommand) (k : Nat) (base : BitVec 64) (answer : Lean.Json) :
    ∃ (result : Result) (plain clean : E2E.Art),
      Stock.lower (source name c runs) = .ok result ∧
      selectWith Stock.lower (source name c runs) = .ok (.stockD0, compact name result) ∧
      pipeT (source name c runs) k base answer = .ok plain ∧
      pipeCleanupT (source name c runs) k base answer = .ok clean ∧
      plain.vc = compact name result ∧ clean.vc = compact name result := by
  have scope := fnScopeB_of_input (source_input_scope name c runs)
  obtain ⟨result, run, selected, lowered⟩ := default_source_success name c runs
  obtain ⟨plain, hp, _, _, _, _⟩ := pipeT_ok scope spillDefinedHyp k base answer
  obtain ⟨clean, hc, _, _, _, _⟩ := pipeCleanupT_ok scope spillDefinedHyp k base answer
  have legacy : lowerFunction (source name c runs) = .ok (compact name result) := by
    rw [← defaultLower_eq_legacy]
    exact lowered
  refine ⟨result, plain, clean, run, selected, hp, hc, ?_, ?_⟩
  · have code := (pipeT_spec hp).1
    rw [legacy] at code
    exact (Except.ok.inj code).symm
  · have code := (pipeCleanupT_spec hc).1
    rw [legacy] at code
    exact (Except.ok.inj code).symm

#print axioms source_input_scope
#print axioms complete_pipeline_witness
end Backend.Stock.D0

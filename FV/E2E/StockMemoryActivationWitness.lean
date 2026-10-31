import FV.E2E.StockMemoryEffectKernel
import FV.E2E.StockMemoryPairedFunctionWitness
import FV.Backend.Proof.StockMemoryCheck
import FV.Backend.Lowering.StockMemoryNI
import FV.Backend.SemanticNICheck

namespace E2E.StockMemoryActivationWitness
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Memory.SingleFixture
set_option autoImplicit false
set_option Elab.async false

/-- The actual Stock artifact passes the memory and production semantic
checkers and is selected by the default memory provider, rather than fallback. -/
theorem default_memory_route_witness : ∃ result,Stock.lower function = .ok result ∧
    Memory.check function result.code = true ∧ SemanticNI.check function result.code = true ∧
    Memory.lowerValidated function = .ok result.code ∧ Memory.SingleClass function := by
  have actual := StockMemoryEffectKernel.actual_effects
  cases run : Stock.lower function with
  | error err => rw [run] at actual; cases actual
  | ok result =>
    rw [run] at actual
    have checked : Memory.check function result.code = true := by
      simp only [Memory.check,StockMemoryEffectKernel.source_checked,run,decide_true,Bool.true_and,actual]
    have semantic : SemanticNI.check function result.code = true := by
      simp only [SemanticNI.check,checked,Bool.or_true,Bool.true_or]
    have chosen : Memory.lowerValidated function = .ok result.code := by
      simp [Memory.lowerValidated,show Memory.eligible function = true from rfl,run,checked]
    exact ⟨result,rfl,checked,semantic,chosen,StockMemoryFunctionWitness.source_class_witness⟩

end E2E.StockMemoryActivationWitness

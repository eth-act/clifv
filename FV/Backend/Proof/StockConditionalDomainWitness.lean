import FV.Backend.Proof.StockConditionalCheck
import FV.Backend.Proof.StockConditionalEmptyTrapFixture
import FV.Backend.Proof.StockConditionalSourceChecks

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual complete returning/trapping sources inhabit the executable checker
and universal production contract. Only fixed original input checks use native
decision; emitted compilation and universal semantics retain their prior trust. -/
theorem checked_conditional_driver_witness : ∃ returning trapping,
    Stock.lower EmptyFixture.function = .ok returning ∧
    Stock.lower EmptyTrapFixture.function = .ok trapping ∧
    Stock.Scalar.Domain EmptyFixture.function ∧ Stock.Scalar.Domain EmptyTrapFixture.function ∧
    Stock.ConditionalCfg.check EmptyFixture.function returning.code = true ∧
    Stock.ConditionalCfg.check EmptyTrapFixture.function trapping.code = true := by
  obtain ⟨returning,returnRun,returnScope,returnDom,rest⟩ := EmptyFixture.driver_witness
  obtain ⟨trapping,trapRun,trapScope,trapDom,more⟩ := EmptyTrapFixture.driver_witness
  obtain ⟨returnChecks,trapChecks⟩ := conditional_source_checks_witness
  exact ⟨returning,trapping,returnRun,trapRun,
    Stock.ConditionalCfg.sourceOk_sound returnChecks,Stock.ConditionalCfg.sourceOk_sound trapChecks,
    by simp [Stock.ConditionalCfg.check,returnChecks,returnRun],
    by simp [Stock.ConditionalCfg.check,trapChecks,trapRun]⟩

end Backend.Stock.Proof.ConditionalValues

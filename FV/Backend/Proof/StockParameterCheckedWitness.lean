import FV.Backend.Proof.StockParameterWitness
import FV.Backend.Lowering.StockParameterCfgNI

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

-- Fixed ORIGINAL source/class/scope/dominance/ABI checks only; no compiler output or simulation fact.
private theorem original_input_checks :
    Stock.ParameterCfg.sourceOk function = true ∧ Stock.ParameterCfg.sourceOk Trap.function = true := by
  native_decide

/-- The checked returning candidate is the actual kernel-compiled Stock artifact. -/
theorem checked_returning_witness : ∃ result,Stock.lower function = .ok result ∧
    Scalar.Domain function ∧ Stock.ParameterCfg.check function result.code = true ∧
    Stock.ParameterCfg.lowerValidated function = .ok result.code := by
  obtain ⟨result,run,tag,reads⟩ := lowered
  have selected : Stock.ParameterCfg.eligible function = true := rfl
  have selectedLeaf : Stock.ParameterCfg.leafEligible function = true := rfl
  have checked : Stock.ParameterCfg.check function result.code = true := by
    simp [Stock.ParameterCfg.check,original_input_checks.1,run]
  exact ⟨result,run,original_domain_witness,checked,by
    simp [Stock.ParameterCfg.lowerValidated,selectedLeaf,run,checked,reads]⟩

/-- A reachable original divide-by-zero path also inhabits the checked provider. -/
theorem checked_trapping_witness : ∃ result,Stock.lower Trap.function = .ok result ∧
    Scalar.Domain Trap.function ∧ Stock.ParameterCfg.check Trap.function result.code = true ∧
    Stock.ParameterCfg.lowerValidated Trap.function = .ok result.code := by
  obtain ⟨result,run,tag,reads⟩ := Trap.lowered
  have selected : Stock.ParameterCfg.eligible Trap.function = true := rfl
  have selectedLeaf : Stock.ParameterCfg.leafEligible Trap.function = true := rfl
  have checked : Stock.ParameterCfg.check Trap.function result.code = true := by
    simp [Stock.ParameterCfg.check,original_input_checks.2,run]
  exact ⟨result,run,Trap.original_domain_witness,checked,by
    simp [Stock.ParameterCfg.lowerValidated,selectedLeaf,run,checked,reads]⟩

end Backend.Stock.Proof.ParameterCfg.Fixture

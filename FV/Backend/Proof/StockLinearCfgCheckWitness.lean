module

public import FV.Backend.Proof.StockLinearCfgFixture
public import FV.Backend.Proof.StockLinearCfgCheck

@[expose] public section

namespace Backend.Stock.Proof.LinearCfgWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

-- witness: native_decide (fixed original-input scope/dominance/ABI checks only)
private theorem input_checks : Stock.LinearCfg.sourceOk function = true := by native_decide

/-- The real three-block source and emitted artifact inhabit every new checked
production-domain theorem, with both edge vectors derived from the run. -/
theorem checked_domain_witness : ∃ result,Stock.lower function = .ok result ∧
    Stock.LinearCfg.eligible function = true ∧ Stock.LinearCfg.check function result.code = true ∧
    Stock.Scalar.Domain function ∧ EdgeLegacyCompatible result.code result.edgeArgs := by
  obtain ⟨result,run,scope,dominated,order⟩ := actual_linear_driver_witness
  have checked : Stock.LinearCfg.check function result.code = true := by
    simp [Stock.LinearCfg.check,input_checks,run]
  obtain ⟨actual,domain,compiled,equal⟩ := Stock.LinearCfg.check_sound checked
  have same : actual = result := Except.ok.inj (compiled.symm.trans run)
  subst actual
  exact ⟨result,run,by decide +kernel,checked,domain,LinearCfg.legacy_compatible run scope
    (entry := function.blocks[0]!) (middle := function.blocks[1]!) (target := function.blocks[2]!)
    (first := ⟨10,[]⟩) (second := ⟨20,[]⟩) (xs := [2])
    rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

end Backend.Stock.Proof.LinearCfgWitness

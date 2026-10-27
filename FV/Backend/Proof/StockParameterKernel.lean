import FV.Backend.Proof.StockParameterFixture
import FV.Backend.ABIReadCfg

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private def snapshot : Bool :=
  match Stock.lower function with
  | .error _ => false
  | .ok result => decide (result.order.nodes[1]? = some (.original 1)) && ABIReadCfg.check function.sig result.code
/-- Actual Stock compilation and its finite ABI read boundary are kernel checked. -/
theorem snapshot_success : snapshot = true := by decide +kernel

theorem lowered : ∃ result,Stock.lower function = .ok result ∧
    result.order.nodes[1]? = some (.original 1) ∧ ABIReadCfg.check function.sig result.code = true := by
  have checked := snapshot_success
  unfold snapshot at checked
  cases run : Stock.lower function with
  | error message => simp only [run] at checked; cases checked
  | ok result =>
    simp only [run,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact ⟨result,rfl,checked⟩

namespace Trap
private def snapshot : Bool :=
  match Stock.lower function with
  | .error _ => false
  | .ok result => decide (result.order.nodes[1]? = some (.original 1)) && ABIReadCfg.check function.sig result.code
/-- Actual Stock compilation and its finite ABI read boundary are kernel checked. -/
theorem snapshot_success : snapshot = true := by decide +kernel

theorem lowered : ∃ result,Stock.lower function = .ok result ∧
    result.order.nodes[1]? = some (.original 1) ∧ ABIReadCfg.check function.sig result.code = true := by
  have checked := snapshot_success
  unfold snapshot at checked
  cases run : Stock.lower function with
  | error message => simp only [run] at checked; cases checked
  | ok result =>
    simp only [run,Bool.and_eq_true,decide_eq_true_eq] at checked
    exact ⟨result,rfl,checked⟩
end Trap
end Backend.Stock.Proof.ParameterCfg.Fixture

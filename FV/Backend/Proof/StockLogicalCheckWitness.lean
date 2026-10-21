import FV.Backend.Proof.StockLogicalCheck
import FV.Backend.Proof.StockLogicalFixtures

namespace Backend.Stock.Logical
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LogicalSemantics
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A nonempty sparse-ID logical source inhabits every source-class guard. -/
theorem classifier_accepts : sourceOk (formFunction .registers) = true := by
  decide +kernel

private def actualChecked : Bool :=
  match Stock.lower (formFunction .registers) with
  | .error _ => false
  | .ok result => check (formFunction .registers) result.code

/-- Fixed-data actual lowering/provenance check; no native axiom enters the
universal checker soundness roots. -/
theorem actualChecked_true : actualChecked = true := by native_decide

/-- A real successful whole-driver output inhabits checker soundness with a
nonempty logical body and the original source domain, without supplied proofs. -/
theorem actual_check_witness :
    ∃ result, Stock.lower (formFunction .registers) = .ok result ∧
      check (formFunction .registers) result.code = true ∧
      Domain (formFunction .registers) ∧
      (formFunction .registers).blocks[0]!.body ≠ [] := by
  have accepted := actualChecked_true
  cases run : Stock.lower (formFunction .registers) with
  | error message => simp only [actualChecked,run] at accepted; cases accepted
  | ok result =>
    simp only [actualChecked,run] at accepted
    exact ⟨result,rfl,accepted,sourceOk_sound classifier_accepts,by decide⟩

end Backend.Stock.Logical

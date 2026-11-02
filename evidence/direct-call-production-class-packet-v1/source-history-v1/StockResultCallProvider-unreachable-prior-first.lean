import FV.E2E.StockResultCallNI
import FV.Backend.Lowering.StockResultCallWith

namespace Backend.Stock.ResultCall
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A successful candidate carries its complete original-source function contract. -/
theorem candidate_domain {f : Clif.Function} {vc : VCode} (accepted : candidate f = .ok vc) :
    Domain f vc := by
  unfold candidate at accepted
  cases lowered : Stock.lower f with
  | error message => simp only [lowered,Except.bind] at accepted; cases accepted
  | ok result =>
    simp only [lowered,Except.bind] at accepted
    split at accepted
    · rename_i checked
      have equal : result.code = vc := Except.ok.inj accepted
      rw [← equal]
      exact check_domain checked
    · cases accepted

/-- The provider keeps every prior result; only a prior error can select this new class. -/
theorem lowerWithPrevious_origin {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : lowerWithPrevious previous f = .ok vc) :
    previous f = .ok vc ∨ (∃ message,previous f = .error message ∧ Domain f vc) := by
  unfold lowerWithPrevious at accepted
  cases original : previous f with
  | ok old =>
    simp only [original] at accepted
    have same : old = vc := Except.ok.inj accepted
    exact Or.inl (same ▸ original)
  | error message =>
    simp only [original] at accepted
    cases chosen : candidate f with
    | error next => simp only [chosen] at accepted; cases accepted
    | ok selected =>
      simp only [chosen] at accepted
      have same : selected = vc := Except.ok.inj accepted
      refine Or.inr ⟨message,original,?_⟩
      exact candidate_domain (same ▸ chosen)

end Backend.Stock.ResultCall

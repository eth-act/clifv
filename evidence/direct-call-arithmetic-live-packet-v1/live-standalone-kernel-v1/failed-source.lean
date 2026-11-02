import FV.E2E.StockLiveCallDomain
import FV.Backend.Lowering.StockLiveCallWith

namespace Backend.Stock.LiveCall
set_option autoImplicit false
set_option Elab.async false

/-- Every selected candidate derives its complete source Domain from the actual finite checks. -/
theorem candidate_domain {f : Clif.Function} {vc : VCode} (accepted : candidate f = .ok vc) :
    Domain f vc := by
  unfold candidate CheckedWith.candidate at accepted
  cases lowered : Stock.lower f with
  | error message => simp only [lowered,bind,Except.bind,pure,Except.pure] at accepted; cases accepted
  | ok result =>
    simp only [lowered,bind,Except.bind,pure,Except.pure] at accepted
    split at accepted
    · rename_i checked
      have equal : result.code = vc := Except.ok.inj accepted
      rw [← equal]
      exact check_domain checked
    · cases accepted

/-- Successful lowering retains the complete predecessor or the proved live-result function class. -/
theorem lowerWithPrevious_origin {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : lowerWithPrevious previous f = .ok vc) :
    previous f = .ok vc ∨ Domain f vc := by
  change (match candidate f with | .ok code => .ok code | .error _ => previous f) = .ok vc at accepted
  cases chosen : candidate f with
  | error message => exact Or.inl (by simpa only [chosen] using accepted)
  | ok code =>
    simp only [chosen] at accepted
    have same : code = vc := Except.ok.inj accepted
    subst code
    exact Or.inr (candidate_domain chosen)

end Backend.Stock.LiveCall

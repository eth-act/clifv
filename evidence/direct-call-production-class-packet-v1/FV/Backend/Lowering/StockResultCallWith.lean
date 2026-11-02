import FV.Backend.StockResultCallCheck

namespace Backend.Stock.ResultCall
set_option autoImplicit false

/-- The caller supplies the complete prior provider; this adapter does not choose a shared chain head. -/
def candidate (f : Clif.Function) : Except String VCode := do
  let result ← Stock.lower f
  if check f result.code then pure result.code
  else throw "Stock direct result caller failed source and result-binding checks"

def lowerWithPrevious (previous : Clif.Function → Except String VCode) (f : Clif.Function) :
    Except String VCode :=
  match candidate f with
  | .ok vc => .ok vc
  | .error _ => previous f

/-- Every rejected candidate retains the complete original provider, including its error. -/
theorem lowerWithPrevious_retry {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {message : String} (failed : candidate f = .error message) :
    lowerWithPrevious previous f = previous f := by
  unfold lowerWithPrevious
  rw [failed]

/-- An admitted class selects its actual Stock artifact, even when the old fallback succeeds. -/
theorem lowerWithPrevious_selects {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : candidate f = .ok vc) :
    lowerWithPrevious previous f = .ok vc := by
  unfold lowerWithPrevious
  rw [accepted]

/-- Every successful candidate retains the actual original Stock result. -/
theorem candidate_stock {f : Clif.Function} {vc : VCode} (accepted : candidate f = .ok vc) :
    ∃ result,Stock.lower f = .ok result ∧ result.code = vc := by
  unfold candidate at accepted
  cases lowered : Stock.lower f with
  | error message => simp only [lowered,bind,Except.bind,pure,Except.pure] at accepted; cases accepted
  | ok result =>
    simp only [lowered,bind,Except.bind,pure,Except.pure] at accepted
    split at accepted
    · exact ⟨result,rfl,Except.ok.inj accepted⟩
    · cases accepted

/-- All earlier Stock successes keep their exact artifact; legacy replacement remains reachable. -/
theorem lowerWithPrevious_preserves {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {result : Stock.Result}
    (stock : Stock.lower f = .ok result) (accepted : previous f = .ok result.code) :
    lowerWithPrevious previous f = .ok result.code := by
  unfold lowerWithPrevious
  cases chosen : candidate f with
  | error message => exact accepted
  | ok next =>
    obtain ⟨actual,run,equal⟩ := candidate_stock chosen
    have same : actual = result := Except.ok.inj (run.symm.trans stock)
    subst actual
    exact congrArg Except.ok equal.symm

/-- Complete retry preserves every previously accepted function. -/
theorem lowerWithPrevious_accepts {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : previous f = .ok vc) :
    ∃ next,lowerWithPrevious previous f = .ok next := by
  unfold lowerWithPrevious
  cases chosen : candidate f with
  | ok next => exact ⟨next,rfl⟩
  | error message => exact ⟨vc,accepted⟩

end Backend.Stock.ResultCall

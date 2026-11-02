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
  match previous f with
  | .ok vc => .ok vc
  | .error message => match candidate f with
    | .ok vc => .ok vc
    | .error _ => .error message

/-- Every rejected candidate retains the complete original provider, including its error. -/
theorem lowerWithPrevious_retry {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {message : String} (failed : candidate f = .error message) :
    lowerWithPrevious previous f = previous f := by
  unfold lowerWithPrevious
  cases original : previous f with
  | ok vc => rfl
  | error priorMessage => rw [failed]

/-- Every prior success retains its exact result, rather than only its acceptance. -/
theorem lowerWithPrevious_preserves {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : previous f = .ok vc) :
    lowerWithPrevious previous f = .ok vc := by
  unfold lowerWithPrevious
  rw [accepted]

/-- The adapter also retains the previous acceptance statement. -/
theorem lowerWithPrevious_accepts {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : previous f = .ok vc) :
    ∃ next,lowerWithPrevious previous f = .ok next := ⟨vc,lowerWithPrevious_preserves accepted⟩

end Backend.Stock.ResultCall

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
  if (sourceData? f).isNone then previous f
  else match candidate f with
    | .ok vc => .ok vc
    | .error _ => previous f

/-- Every rejected candidate retains the exact original provider and source function. -/
theorem lowerWithPrevious_retry {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {message : String} (failed : candidate f = .error message) :
    lowerWithPrevious previous f = previous f := by
  unfold lowerWithPrevious
  split
  · rfl
  · rw [failed]

/-- The adapter preserves acceptance of the complete prior provider. -/
theorem lowerWithPrevious_accepts {previous : Clif.Function → Except String VCode}
    {f : Clif.Function} {vc : VCode} (accepted : previous f = .ok vc) :
    ∃ next,lowerWithPrevious previous f = .ok next := by
  unfold lowerWithPrevious
  split
  · exact ⟨vc,accepted⟩
  · cases chosen : candidate f with
    | ok next => exact ⟨next,rfl⟩
    | error message => exact ⟨vc,accepted⟩

end Backend.Stock.ResultCall

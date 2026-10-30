import FV.Backend.ArithmeticProduction

namespace Backend
set_option autoImplicit false

/-- A successful checked candidate is retained with its actual metadata. -/
theorem lowerCheckedSemanticWith_success
    {lower : Clif.Function → Except String VCode} {f : Clif.Function} {vc : VCode}
    (run : lower f = .ok vc) (checked : Stock.Arithmetic.check f vc = true) :
    lowerCheckedSemanticWith lower f true = .ok vc := by
  simp [lowerCheckedSemanticWith,run,checked]

/-- Candidate failure retries the shipped route with the same function and
verification setting, including its own transactional legacy fallback. -/
theorem lowerCheckedSemanticWith_retry
    {lower : Clif.Function → Except String VCode} {f : Clif.Function} {verify : Bool} {message : String}
    (run : lower f = .error message) :
    lowerCheckedSemanticWith lower f verify =
      lowerCheckedProductionWith Stock.ScalarAdd.lower f verify := by
  simp [lowerCheckedSemanticWith,run,bind,Except.bind]

/-- Rejected candidate data never becomes a verified output. -/
theorem lowerCheckedSemanticWith_rejected
    {lower : Clif.Function → Except String VCode} {f : Clif.Function} {vc : VCode}
    (run : lower f = .ok vc) (rejected : Stock.Arithmetic.check f vc = false) :
    lowerCheckedSemanticWith lower f true =
      lowerCheckedProductionWith Stock.ScalarAdd.lower f true := by
  simp [lowerCheckedSemanticWith,run,rejected,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

end Backend

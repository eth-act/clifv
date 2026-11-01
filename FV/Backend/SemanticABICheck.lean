import FV.Backend.SemanticNICheck
import FV.Backend.StockMemorySretCopyCheck

namespace Backend.SemanticABI
set_option autoImplicit false

/-- Retain every prior verdict and admit the original source-only sret copy class. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  SemanticNI.check f vc || Stock.MemorySretCopy.check f vc

/-- Every prior accepted artifact remains accepted. -/
theorem previous_check {f : Clif.Function} {vc : VCode} (accepted : SemanticNI.check f vc = true) :
    check f vc = true := by simp [check,accepted]

/-- Rejection by the new class retains the exact previous verdict. -/
theorem previous_exact {f : Clif.Function} {vc : VCode} (absent : Stock.MemorySretCopy.check f vc = false) :
    check f vc = SemanticNI.check f vc := by simp [check,absent]

end Backend.SemanticABI

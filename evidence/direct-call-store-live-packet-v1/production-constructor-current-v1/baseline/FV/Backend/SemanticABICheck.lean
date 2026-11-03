import FV.Backend.SemanticNICheck
import FV.Backend.StockMemorySretCopyCheck
import FV.Backend.StockVoidCallNICheck

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

/-- Extend the ABI consumer while retaining every original checker definition and verdict. -/
def checkCalls (f : Clif.Function) (vc : VCode) : Bool :=
  check f vc || Stock.VoidCall.NI.check f vc

theorem previous_check_calls {f : Clif.Function} {vc : VCode} (accepted : check f vc = true) :
    checkCalls f vc = true := by simp [checkCalls,accepted]

theorem previous_exact_calls {f : Clif.Function} {vc : VCode}
    (absent : Stock.VoidCall.NI.check f vc = false) : checkCalls f vc = check f vc := by
  simp [checkCalls,absent]

end Backend.SemanticABI

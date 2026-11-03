import FV.Backend.StockCallStoreCheck
import FV.Backend.StockLiveCallCheck
import FV.Backend.SemanticNICheck
import FV.Backend.StockMemorySretCopyCheck
import FV.Backend.StockVoidCallNICheck
import FV.Backend.StockResultCallCheck

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

namespace Backend.SemanticABI
set_option autoImplicit false

/-- Admit the proved explicit-result caller without changing the previous checker. -/
def checkResultCalls (f : Clif.Function) (vc : VCode) : Bool :=
  checkCalls f vc || Stock.ResultCall.check f vc

theorem previous_check_result_calls {f : Clif.Function} {vc : VCode}
    (accepted : checkCalls f vc = true) : checkResultCalls f vc = true := by
  simp only [checkResultCalls,accepted,Bool.true_or]

theorem previous_exact_result_calls {f : Clif.Function} {vc : VCode}
    (absent : Stock.ResultCall.check f vc = false) : checkResultCalls f vc = checkCalls f vc := by
  simp only [checkResultCalls,absent,Bool.or_false]

end Backend.SemanticABI

namespace Backend.SemanticABI
set_option autoImplicit false

def checkLiveCalls (f : Clif.Function) (vc : VCode) : Bool :=
  checkResultCalls f vc || Stock.LiveCall.check f vc

theorem previous_check_live_calls {f : Clif.Function} {vc : VCode}
    (accepted : checkResultCalls f vc = true) : checkLiveCalls f vc = true := by
  simp only [checkLiveCalls,accepted,Bool.true_or]

theorem previous_exact_live_calls {f : Clif.Function} {vc : VCode}
    (absent : Stock.LiveCall.check f vc = false) : checkLiveCalls f vc = checkResultCalls f vc := by
  simp only [checkLiveCalls,absent,Bool.or_false]
end Backend.SemanticABI

namespace Backend.SemanticABI
set_option autoImplicit false

/-- Add the returned-call store class without changing any prior checker. -/
def checkCallStores (f : Clif.Function) (vc : VCode) : Bool :=
  checkLiveCalls f vc || Stock.CallStore.check f vc

theorem previous_check_call_stores {f : Clif.Function} {vc : VCode}
    (accepted : checkLiveCalls f vc = true) : checkCallStores f vc = true := by
  simp only [checkCallStores,accepted,Bool.true_or]

theorem previous_exact_call_stores {f : Clif.Function} {vc : VCode}
    (absent : Stock.CallStore.check f vc = false) : checkCallStores f vc = checkLiveCalls f vc := by
  simp only [checkCallStores,absent,Bool.or_false]

end Backend.SemanticABI

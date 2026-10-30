import FV.Concurrency.CallArgsEntry

/-!
# Witness for `CallArgsEntry` (#473)

The compiled caller of `atomic_load` (`fC`) passes `callUseRegsC` (`native_decide`, witness
only), the check `callee_argsAtEntry` adds to those of `isel_argsAt`.
-/

namespace Concurrency.CallArgsEntry.Witness

open CallSeg.WitnessC

theorem useRegs_fC : callUseRegsC fC = true := by native_decide

end Concurrency.CallArgsEntry.Witness

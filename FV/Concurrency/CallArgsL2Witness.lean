import FV.Concurrency.CallArgsL2

/-!
# Witness for `CallArgsL2` (#473)

The compiled caller of `atomic_load` (`fC`) passes `callResLenB` (`native_decide`, witness only),
the check `isel_argsAt` adds to those of `resume_allA`.
-/

namespace Concurrency.CallArgsL2.Witness

open CallSeg.WitnessC

theorem resLen_fC : callResLenB fC = true := by native_decide

end Concurrency.CallArgsL2.Witness

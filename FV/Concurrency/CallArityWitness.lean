import FV.Concurrency.CallArity

/-!
# Witness for `CallArity` (#473)

The compiled caller of `atomic_load` (`fC`, whose `call %ld` returns one `i64`) passes the arity
check on the driver's lowering (`native_decide`, witness only): with `CallResumeChecks`' two
checks, `resume_allA` needs no `habi` for it.
-/

namespace Concurrency.CallResumeAll.Witness

open Backend CallArity CallSeg.WitnessC

theorem arity_fC : callArityC fC = true ∧ IselCheck.threadCheckC fC = true := by
  native_decide

end Concurrency.CallResumeAll.Witness

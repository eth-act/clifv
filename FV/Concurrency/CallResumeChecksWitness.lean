import FV.Concurrency.CallLoadData
import FV.Concurrency.CallResumeChecks

/-!
# Witness for `CallResumeChecks` (#473)

The compiled caller of `atomic_load` passes both checks (`native_decide`, witness only), so its
calls define virtual registers only and their def registers are `[x0]`, the callee's `rets`
register: `resume_all`'s `hvdef` and the register part of `habi` from the checks.
-/

namespace Concurrency.CallResumeAll.Witness

open Backend CallResumeChecks CallSeg.WitnessC

theorem checks_fC : callDefsVirtB vcpC = true ∧ callDefsRetB vcpC [.x 0] = true := by
  native_decide

theorem defs_fC : CallDefsVirt vcpC ∧ CallDefsRet vcpC [.x 0] :=
  ⟨(callDefsVirtB_iff _).1 checks_fC.1, (callDefsRetB_iff _ _).1 checks_fC.2⟩

end Concurrency.CallResumeAll.Witness

import FV.E2E.UnwindValueSem
import FV.Backend.Proof.LowerSimURaise

/-!
# The CLIF → VCode layer with unwinding for the dead-cleanup chain (S10e, #232)

The value semantics with unwinding (`valueSemU`) satisfies the generic unwinding interface of
the lowering simulation (`RaiseSem`, `FV/Backend/Proof/LowerSimURaise.lean`): it is `csemU` on
calls and on `loadExtNameGot` (none is a pure producer).
-/

namespace Backend.DeadCleanup

open Backend Backend.Proof

/-- **`RaiseSem` for the value semantics with unwinding.** -/
theorem raiseSem_valueSemU (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) (XR : XRaise) :
    RaiseSem F X XR (valueSemU F ctx X XR) := by
  have h := raiseSem_csemU F ctx X XR
  exact {
    got := fun rd n w => by rw [valueSemU_not_pure rfl]; exact h.got rd n w
    call := fun ci uses w obj w' hr => by rw [valueSemU_call]; exact h.call ci uses w obj w' hr
    tryCall := fun ci ti uses w obj w' hr hok => by
      rw [valueSemU_tryCall]; exact h.tryCall ci ti uses w obj w' hr hok }

end Backend.DeadCleanup

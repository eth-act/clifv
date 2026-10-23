import FV.Link.DeadCleanupCompileT
import FVTest.Link.FloatExeT

/-! Non-vacuity of `Link.DeadCleanup.compileExeT` (S11, #35): on the float program of
`FVTest/Link/FloatExeT` (outside `InScopeP`), `compileExeT` succeeds through its typed branch, so
`compileExeT_correct` applies. Decided by `native_decide` (witness only).
`lake build FVTest.Link.FloatCompileExeT`. -/

namespace E2E.FloatCompileExeTWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend
open E2E.FloatExeTWitness (specC file0C)

def checks : Bool :=
  !InScopeP specC.input0 && (Link.DeadCleanup.compileExeT specC file0C).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **Witness**: the float program is outside `InScopeP` (the typed branch runs). -/
theorem notInScopeP : InScopeP specC.input0 = false := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

def file : ByteArray := getOk (Link.DeadCleanup.compileExeT specC file0C)

theorem compile_eq : Link.DeadCleanup.compileExeT specC file0C = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.2

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct` applies to the float program. -/
theorem correct_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct specC file0C file compile_eq) :=
  @Link.DeadCleanup.compileExeT_correct specC file0C file compile_eq

end E2E.FloatCompileExeTWitness

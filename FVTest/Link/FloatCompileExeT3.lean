module

public import FV.Link.DeadCleanupCompileT3
public import FVTest.Link.FloatExeT

@[expose] public section

/-! Non-vacuity of `Link.DeadCleanup.compileExeT3` (S11, #35): on the float program of
`FVTest/Link/FloatExeT` (outside `InScopeP`, inside `InScopeInT3`), `compileExeT3` succeeds
through its typed branch, so `compileExeT3_correct` applies. Decided by `native_decide`
(witness only). `lake build FVTest.Link.FloatCompileExeT3`. -/

namespace E2E.FloatCompileExeT3Witness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend
open E2E.FloatExeTWitness (specC file0C)

def checks : Bool :=
  !InScopeP specC.input0 && InScopeInT3 specC.input0 &&
    (Link.DeadCleanup.compileExeT3 specC file0C).toBool

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem checks_true : checks = true := by native_decide

/-- **Witness**: the float program is outside `InScopeP` and inside `InScopeInT3`. -/
theorem scope : InScopeP specC.input0 = false ∧ InScopeInT3 specC.input0 = true := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

def file : ByteArray := getOk (Link.DeadCleanup.compileExeT3 specC file0C)

theorem compile_eq : Link.DeadCleanup.compileExeT3 specC file0C = .ok file := by
  have h := checks_true
  simp only [checks, Bool.and_eq_true] at h
  exact getOk_eq h.2

/-- **Witness**: `Link.DeadCleanup.compileExeT3_correct` applies to the float program. -/
theorem correct_spec :
    type_of% (@Link.DeadCleanup.compileExeT3_correct specC file0C file compile_eq) :=
  @Link.DeadCleanup.compileExeT3_correct specC file0C file compile_eq

end E2E.FloatCompileExeT3Witness

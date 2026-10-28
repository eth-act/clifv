import FV.Link.DeadCleanupExePeakT
import FVTest.Link.FloatExeT
import FVTest.Link.FloatCompileExeT

/-! Non-vacuity of the typed dead-cleanup peak theorems (S11e6, #419): on the float program of
`FVTest/Link/FloatExeT` (float data movement, float parameters and returns), the typed compiler
`Link.DeadCleanup.compileExeT` succeeds (`E2E.FloatCompileExeTWitness.compile_eq`), so
`Link.DeadCleanup.compileExeT_correct_peak` applies; and
`Link.DeadCleanup.compileExe_correct_peakT` applies to the `leanLink` facts of
`E2E.FloatExeTWitness` for the same program (`specC`). Decided by `native_decide` (witness only).
`lake build FVTest.Link.FloatCompileExeTPeak`. -/

namespace E2E.FloatCompileExeTPeakWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend
open E2E.FloatExeTWitness (specC file0C fileC parts link_eqC)
open E2E.FloatCompileExeTWitness (file compile_eq)

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct_peak` applies to the float program. -/
theorem correct_peakT_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct_peak specC file0C file compile_eq) :=
  @Link.DeadCleanup.compileExeT_correct_peak specC file0C file compile_eq

/-- **Witness**: `Link.DeadCleanup.compileExe_correct_peakT` applies to the float program. -/
theorem correct_peakT_specC :
    type_of% (@Link.DeadCleanup.compileExe_correct_peakT specC file0C fileC
      parts.2.2.2.2.1 parts.2.2.2.2.2.1 link_eqC) :=
  @Link.DeadCleanup.compileExe_correct_peakT specC file0C fileC parts.2.2.2.2.1
    parts.2.2.2.2.2.1 link_eqC

end E2E.FloatCompileExeTPeakWitness

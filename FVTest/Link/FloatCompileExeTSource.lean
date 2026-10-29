module

public import FV.Link.DeadCleanupExeSourceT
public import FVTest.Link.FloatExeT
public import FVTest.Link.FloatCompileExeT

@[expose] public section

/-! Non-vacuity of the typed source theorems (S11e6, #419): the float program of
`FVTest/Link/FloatExeT` (float data movement, float parameters and returns) is in the source
domain (`SrcScopeB`), and `Link.DeadCleanup.compileExeT` succeeds on it through its typed branch
(`E2E.FloatCompileExeTWitness.compile_eq`), so `Link.DeadCleanup.compileExeT_correct_source` and
`compileExeT_correct_source_peak` apply; `compileExe_correct_sourceT` and
`compileExe_correct_source_peakT` apply to the `leanLink` facts of `E2E.FloatExeTWitness` for the
same program (`specC`). Decided by `native_decide` (witness only).
`lake build FVTest.Link.FloatCompileExeTSource`. -/

namespace E2E.FloatCompileExeTSourceWitness
set_option autoImplicit false
open E2E E2E.LinkCheck Link Backend
open E2E.FloatExeTWitness (specC file0C fileC parts link_eqC)
open E2E.FloatCompileExeTWitness (file compile_eq)

/-- The float program is in the source domain. -/
theorem srcOk : SrcScopeB specC.inputCleanup = true := by native_decide

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct_source` applies to the float program. -/
theorem source_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct_source specC file0C file compile_eq srcOk) :=
  @Link.DeadCleanup.compileExeT_correct_source specC file0C file compile_eq srcOk

/-- **Witness**: `Link.DeadCleanup.compileExeT_correct_source_peak` applies to the float
program. -/
theorem source_peak_spec :
    type_of% (@Link.DeadCleanup.compileExeT_correct_source_peak specC file0C file compile_eq
      srcOk) :=
  @Link.DeadCleanup.compileExeT_correct_source_peak specC file0C file compile_eq srcOk

/-- **Witness**: `Link.DeadCleanup.compileExe_correct_sourceT` applies to the float program. -/
theorem sourceT_specC :
    type_of% (@Link.DeadCleanup.compileExe_correct_sourceT specC file0C fileC
      parts.2.2.2.2.1 parts.2.2.2.2.2.1 link_eqC srcOk) :=
  @Link.DeadCleanup.compileExe_correct_sourceT specC file0C fileC parts.2.2.2.2.1
    parts.2.2.2.2.2.1 link_eqC srcOk

/-- **Witness**: `Link.DeadCleanup.compileExe_correct_source_peakT` applies to the float
program. -/
theorem source_peakT_specC :
    type_of% (@Link.DeadCleanup.compileExe_correct_source_peakT specC file0C fileC
      parts.2.2.2.2.1 parts.2.2.2.2.2.1 link_eqC srcOk) :=
  @Link.DeadCleanup.compileExe_correct_source_peakT specC file0C fileC parts.2.2.2.2.1
    parts.2.2.2.2.2.1 link_eqC srcOk

end E2E.FloatCompileExeTSourceWitness

import Crates.CompileExeWitness
import FV.Link.ExeInputReachCleanup

/-! # Non-vacuity of the executable compiler's totality on input conditions (L1e) on a survey crate

`total_reach_witness`: every hypothesis of `Link.compileExe_total_reach` holds on `a_arith`'s 58
functions with the Lean compiler's layout (`spec.placed`) and the executable with a `PT_TLS`
segment of `Crates.CompileExeWitness` (`file0T`): the input conditions of
`total_input_witness` and the reach of the CLIF functions' references from the region
(`reachOkB`, decided on the CLIF functions and the link map). `total_reach_cleanup_witness`: the
same for the shipped compiler (`Link.DeadCleanup.compileExe_total_reach`).
-/

namespace Crates.CompileExeReachWitness

open E2E E2E.LinkCheck Link Crates.LeanLinkWitness Crates.CompileExeWitness

/-- The references of `a_arith`'s functions are in reach of the Lean compiler's region. -/
theorem reachT : spec.placed.reachOkB = true := by native_decide

/-- **Non-vacuity of `compileExe_total_reach`** on `a_arith`. -/
theorem total_reach_witness :
    compileExe spec.placed file0T =
      .ok (patch file0T (offsetOf phsT spec.R) (regionOf spec.placed (Elf.tpOff phsT))) :=
  compileExe_total_reach inScopeT layoutT hphT file0T_ok reachT

/-- The references of `a_arith`'s functions are in reach of the shipped compiler's region. -/
theorem reachC : (DeadCleanup.placed spec).reachOkB = true := by native_decide

/-- **Non-vacuity of `DeadCleanup.compileExe_total_reach`** on `a_arith`. -/
theorem total_reach_cleanup_witness :
    DeadCleanup.compileExe (DeadCleanup.placed spec) file0C =
      .ok (patch file0C (offsetOf phsC spec.R)
        (DeadCleanup.regionOf (DeadCleanup.placed spec) (Elf.tpOff phsC))) :=
  DeadCleanup.compileExe_total_reach inScopeC layoutC hphC file0C_ok reachC

end Crates.CompileExeReachWitness

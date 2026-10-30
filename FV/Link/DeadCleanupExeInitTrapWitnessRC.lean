import FV.Link.DeadCleanupExeInitTrapWitnessR
import FV.Link.DeadCleanupExeInitRC
import FV.E2E.DeadCleanupBinaryInitClosed

/-!
# Witness: the trapping executable theorem on decidable checks, no premise (SEM1 #537, #713)

`f(x) = 1 / x` (`DeadCleanupExeInitTrapWitnessR`) under `compileExe_correct_initRCT`: the closed
base discharges `BaseRetOk`, `HooksKeep` and `BaseNIX`, the code checks are decided
(`initChecksB_true`), so **`divz_traps_initRC`** has no premise.
-/

namespace Link.DeadCleanup.InitTrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

/-- The oracle route's code checks hold on the compiled program. -/
theorem initChecksB_true : (sys I B).initChecksB = true := by native_decide

/-- **The executable traps with `int_divz`, decidable checks, no premise** (module doc). -/
theorem divz_traps_initRC :
    ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped .intDivz) :=
  compileExe_correct_initRCT compile_eq B baseOk (hooksSim_closed _) hf hc M0 intact outsideCall
    clifRunB initChecksB_true (baseRetOk_closedSys I) (hooksKeep_closedSys I)
    (baseNIX_closed fF rC _) (trapsExplicit _ _) run_traps

end Link.DeadCleanup.InitTrapWitness

import FV.Link.DeadCleanupExeInitTrapWitnessR
import FV.Link.DeadCleanupExeInitRU

/-!
# Witness: the trapping executable theorem under `InitOkRU`, no premise left (SEM1 #537, #732)

`divz_traps_initR` (`DeadCleanupExeInitTrapWitnessR`) rests on `InitOkR`, which cannot be
constructed (#732). With `compileExe_correct_initTRU` the oracle route's premises are needed only
under `NeedSlots`; `f(x) = 1 / x` has no stack slots (`not_needSlots`), so `InitOkRU` holds
(`InitOkRU.of_not_needSlots`) and **`divz_traps_initRU`** has no premise: the executable's run
from `rC` (`x0 = 0`) reaches the trap site with `int_divz`.
-/

namespace Link.DeadCleanup.InitTrapWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

/-- `InitOkRU` of the proof's system: no program callee has slots. -/
theorem initOkRU : InitOkRU (sysS I B fF rC (GotSlot I file)) (kapW I B fF rC) :=
  InitOkRU.of_not_needSlots not_needSlots

/-- **The executable traps with `int_divz`, no premise** (module doc). -/
theorem divz_traps_initRU :
    ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped .intDivz) :=
  compileExe_correct_initTRU compile_eq B baseOk (hooksSim_closed _) hf hc M0 intact outsideCall
    clifRunB initOkRU (trapsExplicit _ _) run_traps

end Link.DeadCleanup.InitTrapWitness

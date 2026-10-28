import FV.Link.DeadCleanupExeInitSlotWitnessR
import FV.Link.DeadCleanupExeInitRU
import FV.E2E.DeadCleanupBinaryInitClosed

/-!
# Witness: the stale read under `InitOkRU`, scope conditions discharged (SEM1 #537, #732)

`stale_read_returns_initR` (`DeadCleanupExeInitSlotWitnessR`) rests on `InitOkR`, which cannot be
constructed (#732). Under `compileExe_correct_initRU` the closed base discharges `BaseRetOk` and
`HooksKeep` (`baseRetOk_closed`, `hooksKeep_closed`) and `retCountB` decides `RetCount`
(`retCountB_all`): **`stale_read_returns_initRU`** has only the determinism premises `DetPRBRU`
and `CallTwinCE` of the proof's system left (the program needs the oracle: `h` and `r` have
slots).
-/

namespace Link.DeadCleanup.InitSlotWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

theorem retCountB_all : (prog I).funcs.all ((sys I B).retCountB ·) = true := by native_decide

/-- **The executable returns `82` on a stale read, under the determinism premises only**
(module doc). -/
theorem stale_read_returns_initRU
    (hdet : ∀ M, (sysS I B fF rC (GotSlot I file)).std.DetPRBRU (kapW I B fF rC) M)
    (htw : ∀ M, (sysS I B fF rC (GotSlot I file)).std.CallTwinCE (kapW I B fF rC) M) :
    ∃ v cm, v.ty = .i64 ∧ v.bits.toNat = 82 ∧
      ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
        (E2E.DeadCleanupBinCheck.RelocAt I) (.returned [v] cm) := by
  obtain ⟨v, m, -, hr, hty, hv⟩ := run_init
  exact ⟨v, m, hty, hv, compileExe_correct_initRU compile_eq B baseOk (hooksSim_closed _) hf hc M0
    intact outsideCall clifRunB
    ⟨fun _ => baseRetOk_closed I fF rC _, fun _ => retCount_of_B retCountB_all, fun _ => hdet,
      fun _ => htw, fun _ => hooksKeep_closed I fF rC _⟩ hr⟩

end Link.DeadCleanup.InitSlotWitness

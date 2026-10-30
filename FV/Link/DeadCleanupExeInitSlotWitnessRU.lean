import FV.Link.DeadCleanupExeInitSlotWitness
import FV.Link.DeadCleanupExeInitRC
import FV.E2E.DeadCleanupBinaryInitClosed

/-!
# Witness: the stale read under the slot-byte oracle, no premise left (SEM1 #537, #713, #732)

`stale_read_returns_initR` (`DeadCleanupExeInitSlotWitnessR`) rests on `InitOkR`, which cannot be
constructed (#732). Under `compileExe_correct_initRC` the closed base discharges `BaseRetOk`,
`HooksKeep` and `BaseNIX` (`baseRetOk_closedSys`, `hooksKeep_closedSys`, `baseNIX_closed`) and
the code checks are decided (`initChecksB_true`; `retCountB_all` is its `RetCount` part):
**`stale_read_returns_initRU`** has no premise (the program needs the oracle: `h` and `r` have
slots), and is a witness of `compileExe_correct_initRC`.
-/

namespace Link.DeadCleanup.InitSlotWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

theorem retCountB_all : (prog I).funcs.all ((sys I B).retCountB ·) = true := by native_decide

/-- The oracle route's code checks hold on the compiled program. -/
theorem initChecksB_true : (sys I B).initChecksB = true := by native_decide

/-- **The executable returns `82` on a stale read, no premise** (module doc). -/
theorem stale_read_returns_initRU :
    ∃ v cm, v.ty = .i64 ∧ v.bits.toNat = 82 ∧
      ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
        (E2E.DeadCleanupBinCheck.RelocAt I) (.returned [v] cm) := by
  obtain ⟨v, m, -, hr, hty, hv⟩ := run_init
  exact ⟨v, m, hty, hv, compileExe_correct_initRC compile_eq B baseOk (hooksSim_closed _) hf hc M0
    intact outsideCall clifRunB initChecksB_true (baseRetOk_closedSys I) (hooksKeep_closedSys I)
    (baseNIX_closed fF rC _) hr⟩

end Link.DeadCleanup.InitSlotWitness

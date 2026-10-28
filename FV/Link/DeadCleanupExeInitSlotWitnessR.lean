import FV.Link.DeadCleanupExeInitSlotWitness
import FV.Link.DeadCleanupExeInitR

/-!
# Witness: the stale read under the corrected premises (SEM1 #537, #719, #716)

`stale_read_returns_init` (`DeadCleanupExeInitSlotWitness`) with `compileExe_correct_initR`: the
executable of `{f, h, r}` returns `82` from the caller state `rC` (`r` reads the bytes `h` left in
its slot), under the corrected oracle-route premises `InitOkR` only (the entry contract is
discharged, `outsideCall`).
-/

namespace Link.DeadCleanup.InitSlotWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend Backend.Proof
  Backend.Proof.Driver

/-- **The executable returns `82` on a stale read, corrected premises** (module doc). -/
theorem stale_read_returns_initR
    (hIO : InitOkR (sysS I B fF rC (GotSlot I file)) (kapW I B fF rC)) :
    ∃ v cm, v.ty = .i64 ∧ v.bits.toNat = 82 ∧
      ExecRefines (art I fF).fb (art I fF).base (xreg 30 rC) (step I B file) rC
        (E2E.DeadCleanupBinCheck.RelocAt I) (.returned [v] cm) := by
  obtain ⟨v, m, -, hr, hty, hv⟩ := run_init
  exact ⟨v, m, hty, hv, compileExe_correct_initR compile_eq B baseOk (hooksSim_closed _) hf hc M0
    intact outsideCall clifRunB hIO hr⟩

end Link.DeadCleanup.InitSlotWitness

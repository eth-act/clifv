import FV.Concurrency.ArmAllocLinked
import FV.Concurrency.ArmAllocPauseWitness

/-!
# Layer 4b on a linked machine: witness (T2j follow-up, #473)

The linked machine `MC2` of the compiled caller of `atomic_load` (the callee's code on its
program, the switch back to the caller's program at the callee's `ret` line, the caller's
`RC.step` on the caller's program) agrees with `RC.step` at the caller's lines
(`agreesAt_MC2`); `caller_lsCL`: `arm_alloc_refines_lsCL` on `MC2`'s runs from the caller's body
entry after the prologue.
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof Backend.Proof.Driver
  VCodeThread PrepThread AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot Code
  RealizeCompiled RealizeCompiled.Witness RealizeCompiled.WitnessL CallThread

/-- **The linked machine agrees with the caller's step on the caller's program.** -/
theorem agreesAt_MC2 : AgreesAt RC MC2 := fun _ hx _ => mc2_caller hx

/-- **Non-vacuity of `arm_alloc_refines_lsCL`**: the runs of the linked machine `MC2` from the
caller's body entry after the prologue are realized entirely, or up to a state related to where
its allocated code is done or pauses at its call or its return. -/
theorem caller_lsCL {mon : Mon} {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm MC2 (OkPriv RC)
      (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length RC.s0, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun RC.vc RC.rf RC.sem ckeep (cEvs RC.F RC.ctx)
        (MConf.init RC.rf (locVal RC.fr (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length
          RC.s0)) w₀C) trS cE ∧
      ThreadRefine.Refines (· = ·) (PrivA RC) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧
      (n = ls.length ∨ ∃ tE, PRun Policy.arm MC2 (OkPriv RC)
        (iterN RC.step (prologueLines RC.af.saves RC.af.frameSize RC.af.isCaller).length RC.s0, mon) (ls.take n) tE ∧
        RelQ RC tE cE ∧ Pause RC cE) := by
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  exact arm_alloc_refines_lsCL wfRC scopeRC agreesAt_MC2 hq hA hr

end Concurrency.CallSeg.WitnessC

import FV.Concurrency.CallRetLink
import FV.Concurrency.LinkedMachineWitness

/-!
# Witness: the return end on the linked machine (#473, step (4))

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`):
the return address after the caller's `bl` (`RC.pcOf 24 + 4`) is outside the callee's code and
inside the caller's (`ra_out`, `ra_in`, `native_decide`, witness only), so **`ret_end_ld`**:
`Link.ret_end` for every activation of `atomic_load` entered with that return address, at every
`rets` pause with its contract `RetEnd`.
-/

namespace Concurrency.LinkedMachine.Witness

open Arm ArmThread Backend Backend.Proof E2E ArmAllocThread CallRetsEnd CallSeg.WitnessC

theorem ra_out : ∀ k < ldF.fb.words.size, RC.pcOf 24 + 4#64 ≠ ldF.base + BitVec.ofNat 64 (4 * k) := by
  native_decide

theorem ra_in : callerF.InRange (RC.pcOf 24 + 4#64) := by
  native_decide

/-- **The callee's return on the linked machine** (module doc). -/
theorem ret_end_ld {s0 : ArmState} {env : Clif.Env} {p : Clif.Program} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State}
    (hRB : (link2.act ldF s0 0 RC.F).Wf) (hent : AbiCall ldF.fb ldF.base (RC.pcOf 24 + 4#64) s0)
    (hret : RetEnd (link2.act ldF s0 0 RC.F) (RC.pcOf 24 + 4#64) env p MR slots r₀ x s') :
    ∃ n, 0 < n ∧ RetC (link2.act ldF s0 0 RC.F) (RC.pcOf 24 + 4#64) r₀
      (iterN (link2.act ldF s0 0 RC.F).step n x) := by
  obtain ⟨n, hn, hRC, -⟩ := Link.ret_end ok2 (nB := "ld") (by simp [link2]) hRB hent ra_out
    (nA := "f") (by simp [link2]) ra_in hret
  exact ⟨n, hn, hRC⟩

end Concurrency.LinkedMachine.Witness

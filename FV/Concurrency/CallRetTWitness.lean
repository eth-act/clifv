import FV.Concurrency.CallRetT
import FV.Concurrency.CallRetLinkWitness

/-!
# Witness: the callee's return end as a `RealizedT` (#473, step (4))

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`,
the return address of `ret_end_ld`): **`ret_T_ld`**, `CallRetT.realizedT_ret` for every
activation of `atomic_load` at every `rets` pause with its contract and the CLIF state at its
`return`, below the caller's frame.
-/

namespace Concurrency.CallRetT.Witness

open Arm ArmThread Backend Backend.Proof E2E ArmAllocThread CallRetsEnd CallSeg.WitnessC
  LinkedMachine LinkedMachine.Witness IselCallRet

theorem ret_T_ld {s0 : ArmState} {env : Clif.Env} {p : Clif.Program} {MR : MemRelT}
    {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State}
    (hRB : (link2.act ldF s0 0 RC.F).Wf) (hent : AbiCall ldF.fb ldF.base (RC.pcOf 15 + 4#64) s0)
    (hret : RetEnd (link2.act ldF s0 0 RC.F) (RC.pcOf 15 + 4#64) env p MR slots r₀ x s')
    (hat : AtRetS s') (hcall : s'.callers = []) :
    ∃ n vals cm, 0 < n ∧ Clif.step env p s' = .done vals cm ∧
      RetC (link2.act ldF s0 0 RC.F) (RC.pcOf 15 + 4#64) r₀
        (iterN (link2.act ldF s0 0 RC.F).step n x) := by
  obtain ⟨n, vals, cm, hn, hd, hRC, -⟩ := realizedT_ret (Bnd := fun _ => True) ok2 (nB := "ld")
    (by simp [link2]) hRB hent ra_out (nA := "f") (by simp [link2]) ra_in hret hat hcall
    (fun _ _ => trivial)
  exact ⟨n, vals, cm, hn, hd, hRC⟩

end Concurrency.CallRetT.Witness

import FV.Concurrency.CallRets
import FV.Concurrency.CallLoadFull

/-!
# Witness: the CLIF return pop in a linked thread (#473)

**`ret_pop_L`**: `CallRets.ret_pop` on the compiled `atomic_load`'s CLIF state after its load
(`CallSeg.WitnessC.stepLd`, ready to `return v1`) under the caller's suspended frame `extC`.
-/

namespace Concurrency.CallRets.Witness

open ClifThread CallSeg.WitnessC

/-- **The callee's return pops to the caller** (module doc). -/
theorem ret_pop_L (env : Clif.Env) :
    ∃ s1 regs cm, CStep env pCL (.run (ClifLift.pushC extC s1)) []
      (.run ⟨{ ({ csC.frame with body := [] } : Clif.Frame) with regs := regs }, [], cm⟩) := by
  obtain ⟨s1, -, ⟨hb1, hT1, -, hf1, v, hv⟩, hcl1⟩ :=
    stepLd env (fun _ => some 0) (fun _ _ => rfl)
  have hret := clifF.2.1
  have hs : Clif.step env pCL s1 =
      .done [⟨.i64, v⟩] ((s1.mem.free (s1.frame.slots.map (·.2))).leave) := by
    rw [Clif.step_term env pCL _ hb1, hT1]
    simp [Clif.stepTerm, Clif.Frame.getMany, Clif.Frame.get, hv, Clif.returnValues, Clif.checkTys,
      Clif.Res.check, hf1, hret, hcl1]
  exact ⟨s1, _, _, ret_pop hcl1 hb1 hT1 hs rfl⟩

end Concurrency.CallRets.Witness

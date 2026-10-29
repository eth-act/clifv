module

public import FV.Concurrency.CallEnterClif
public import FV.Concurrency.CallLoadWitness

@[expose] public section

/-!
# Witness for `CallEnterClif` (#473)

`enter_C`: the compiled caller's call of `%ld` (`CallLoadWitness.stepC`) enters `%ld` with the
argument values of the call's use `v0`: the entered state is `pushC` of the caller's frame over
`%ld`'s own entry state, with the facts `arm_isel_refines_entryCRN` asks of it.
-/

namespace Concurrency.CallSeg.WitnessC

open Prog ClifThread ClifThreadI Concurrency.CallEnterClif

theorem extC_some : csC.frame.func.extern? 0 = some extF := by native_decide

theorem enter_C (env : Clif.Env) :
    ∃ vals B0 cs, csC.frame.getMany [0] = .ok vals ∧ RealizeCompiled.WitnessL.fL.blocks[0]? = some B0 ∧
      CStepI env pCL (.run csC, fun _ => False) []
        (.run (ClifLift.pushC (({ csC.frame with body := [] }, [1]) :: csC.callers) cs),
          fun a => False ∨ slotZ RealizeCompiled.WitnessL.fL csC.mem a) ∧
      cs.callers = [] ∧ cs.frame.func = RealizeCompiled.WitnessL.fL ∧
      cs.frame.slots = (Clif.enterSlots RealizeCompiled.WitnessL.fL csC.mem).1 ∧
      cs.mem = (Clif.enterSlots RealizeCompiled.WitnessL.fL csC.mem).2 ∧
      cs.frame.body = B0.body ∧ cs.frame.term = B0.term ∧
      Clif.Regs.empty.setMany (B0.params.map (·.1)) vals = some cs.frame.regs ∧
      vals.map (·.ty) = B0.params.map (·.2) ∧ vals.map (·.ty) = RealizeCompiled.WitnessL.fL.sig.params.map (·.ty) :=
  cstepI_call_entry (rest := []) clifC.1 extC_some clifC.2.1 (stepC env csC.mem.bytes) _
    (fun pl h => by cases h)

end Concurrency.CallSeg.WitnessC

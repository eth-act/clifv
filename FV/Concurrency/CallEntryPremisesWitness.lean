import FV.Concurrency.CallEntryPremises
import FV.Concurrency.CallLoadWitness

/-!
# Witness: the callee's entry premises (#473, step (3))

**`entry_premises_L`**: `ArmAllocThread.entry_premises` for the compiled `atomic_load` entered
(`CallSeg.WitnessC.RLx`, `enterL`) from any caller state `s` related to the compiled caller
(`StRel RC`): the callee's checker entry values of the callee-saved registers are `s`'s, its
entry `sp` is `s`'s, its return address the address after the `bl`.
-/

namespace Concurrency.CallSeg.WitnessC

open Arm ArmThread Backend Backend.Proof E2E ArmAllocThread

theorem xreg30_enterL (s : ArmState) : xreg 30 (enterL s) = Arm.r .PC s + 4#64 := by
  simp only [xreg, enterL]
  rw [r_of_w_different (by decide), r_of_w_same]

/-- **The callee's entry premises for the compiled `atomic_load`** (module doc). -/
theorem entry_premises_L {s : ArmState} {m : Loc → CV} (hS : StRel RC s m w₀C) :
    (∀ r ∈ calleeSaved,
      ckeep r (locVal (RLx s).fr (iterN (RLx s).step
        (prologueLines (RLx s).af.saves (RLx s).af.frameSize (RLx s).af.isCaller).length (RLx s).s0) (.reg r)) =
        ckeep r (regVal s r)) ∧
    spv (RLx s).s0 = spOf s ∧ Arm.r .PC s + 4#64 = Arm.r .PC s + 4#64 :=
  entry_premises (wfX hS) (abiX hS) (fun f h1 h2 => r_enterL h1 h2 s) (xreg30_enterL s)

end Concurrency.CallSeg.WitnessC

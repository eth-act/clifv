import FV.Concurrency.AllocThread
import FV.Concurrency.FrameEvs

/-!
# The callee's entry premises of the caller's resume (#473, step (3))

`CallRetResume.resume_premises_of_retEnd` asks, of a callee entered at the caller's call, that
its checker entry values of the callee-saved registers be the caller's (`hr₀`), its entry `sp`
the caller's (`hsp0`) and its return address the address after the call (`hra`). For a callee
whose ABI entry state differs from the caller's state at the call only in the pc and `x30`
(the `bl`/`blr`'s link) these hold:

* `prologue_fields`, `regVal_calleeSaved_congr` (`FrameEvs`): the prologue keeps every field
  but the pc, x29, `sp` and x16; a callee-saved register's value depends on fields other than
  those and x30;
* **`entry_premises`**: `hr₀` (with the entry values of `CallLayers.alloc_init` after
  `ArmAllocEntry.q_init_lines`: the registers after the prologue), `hsp0` and `hra`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
  E2E

/-- **The callee's entry premises of the caller's resume** (module doc): a callee `RB` whose ABI
entry state agrees with the caller's state `x` at its call but in the pc and `x30`, which holds
the address after the call. -/
theorem entry_premises {RB : RL} (hRB : RB.Wf) {ra : BitVec 64}
    (hent : AbiCall RB.fb RB.base ra RB.s0) {x : ArmState}
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64) :
    (∀ r ∈ calleeSaved,
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize RB.af.isCaller).length RB.s0) (.reg r)) =
        ckeep r (regVal x r)) ∧
    spv RB.s0 = spOf x ∧ ra = Arm.r .PC x + 4#64 := by
  refine ⟨fun r hr => ?_, hfx _ (by simp) (by simp), hent.lr.symm.trans hlr⟩
  have e := regVal_calleeSaved_congr (s := iterN RB.step (prologueLines RB.af.saves RB.af.frameSize RB.af.isCaller).length RB.s0)
    (t := x) (fun f h1 h2 h3 h4 h5 => (prologue_fields hRB hent f h1 h3 h5 h2).trans (hfx f h1 h4)) r hr
  simp only [locVal]
  rw [e]

end Concurrency.ArmAllocThread

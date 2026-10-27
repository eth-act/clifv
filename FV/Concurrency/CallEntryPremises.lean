import FV.Concurrency.CallRetResume

/-!
# The callee's entry premises of the caller's resume (#473, step (3))

`CallRetResume.resume_premises_of_retEnd` asks, of a callee entered at the caller's call, that
its checker entry values of the callee-saved registers be the caller's (`hr₀`), its entry `sp`
the caller's (`hsp0`) and its return address the address after the call (`hra`). For a callee
whose ABI entry state differs from the caller's state at the call only in the pc and `x30`
(the `bl`/`blr`'s link) these hold:

* `prologue_fields`: the prologue keeps every field but the pc, x29, `sp` and x16;
* `regVal_calleeSaved_congr`: a callee-saved register's value depends on fields other than
  those and x30;
* **`entry_premises`**: `hr₀` (with the entry values of `CallLayers.alloc_init` after
  `ArmAllocEntry.q_init_lines`: the registers after the prologue), `hsp0` and `hra`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
  E2E

/-- **The prologue keeps every field but the pc, x29, `sp` and x16.** -/
theorem prologue_fields {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) :
    ∀ f, f ≠ .PC → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → f ≠ .GPR 16#5 →
      Arm.r f (iterN R.step (prologueLines R.af.saves R.af.frameSize).length R.s0) = Arm.r f R.s0 := by
  have hst0 := hR.stack.frame
  have hs : R.af.frameSize < 2 ^ 64 := by have := hst0.1; omega
  have hal0 : Arm.CheckSPAlignment R.s0 := (checkSP_iff _).2 hent.spAligned
  obtain ⟨vb, items, code, ls, ps1, ps2, T, hvb, hit, hcode, hls, htr, hj0, hdrop⟩ := entry_block hR
  obtain ⟨s', hsteps, -, -, ho', -⟩ := prologue_ok (R.envOf 1) hs R.s0 hal0
  have hpc1 : Arm.r .PC R.s0 = R.pcOf 1 := by
    rw [hent.pc]
    simp only [RL.pcOf, RL.L] at hj0 ⊢
    rw [lineOffset_succ _ _ _ hj0]
    simp [lineOffset, Line.size]
  obtain ⟨hiter, -, -, -⟩ := iterN_steps hR hdrop
    (fun ln h => by obtain ⟨x, e, hh, -⟩ := prologueLines_ins _ ln h; exact ⟨x, e, hh⟩)
    hent.program hpc1 hent.err hsteps
  rw [hiter]
  exact ho'

/-- A callee-saved register's value depends on fields other than the pc, x16, x29, x30 and
`sp`. -/
theorem regVal_calleeSaved_congr {s t : ArmState}
    (h : ∀ f, f ≠ .PC → f ≠ .GPR 16#5 → f ≠ .GPR 29#5 → f ≠ .GPR 30#5 → f ≠ .GPR 31#5 →
      Arm.r f s = Arm.r f t) :
    ∀ r ∈ calleeSaved, regVal s r = regVal t r := by
  intro r hr
  simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have hne : ∀ n, n < 32 → n ≠ 19 + i →
        StateField.GPR (rnum (19 + i)) ≠ StateField.GPR (BitVec.ofNat 5 n) := by
      intro n hn hni he
      injection he with he'
      have := congrArg BitVec.toNat he'
      simp [rnum] at this
      omega
    simp only [regVal]
    rw [h _ (by simp) (hne 16 (by omega) (by omega)) (hne 29 (by omega) (by omega))
      (hne 30 (by omega) (by omega)) (hne 31 (by omega) (by omega))]
  · simp only [regVal]
    exact h _ (by simp) (by simp) (by simp) (by simp) (by simp)

/-- **The callee's entry premises of the caller's resume** (module doc): a callee `RB` whose ABI
entry state agrees with the caller's state `x` at its call but in the pc and `x30`, which holds
the address after the call. -/
theorem entry_premises {RB : RL} (hRB : RB.Wf) {ra : BitVec 64}
    (hent : AbiCall RB.fb RB.base ra RB.s0) {x : ArmState}
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64) :
    (∀ r ∈ calleeSaved,
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0) (.reg r)) =
        ckeep r (regVal x r)) ∧
    spv RB.s0 = spOf x ∧ ra = Arm.r .PC x + 4#64 := by
  refine ⟨fun r hr => ?_, hfx _ (by simp) (by simp), hent.lr.symm.trans hlr⟩
  have e := regVal_calleeSaved_congr (s := iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0)
    (t := x) (fun f h1 h2 h3 h4 h5 => (prologue_fields hRB hent f h1 h3 h5 h2).trans (hfx f h1 h4)) r hr
  simp only [locVal]
  rw [e]

end Concurrency.ArmAllocThread

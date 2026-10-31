import FV.Concurrency.CallRetResume
import FV.Concurrency.CallEntryPremises

/-!
# The callee's return contract relative to its entry (#473, step (3))

`CallRetResume.resume_premises_of_retEnd` asks, besides the entry premises of
`CallEntryPremises.entry_premises`, that the callee's run up to its `rets` pause keep the
caller's frame and kept addresses `RA.FK` (`hmr`). That fact needs no event-level argument: the
register-level relation `Q` carries `StRel.gkeep` (the activation's kept addresses `RB.G` hold
their entry bytes), which survives interference (`ArmAllocThread.stRel_patch`: patches avoid
`RB.F ⊇ RB.G`) and the activation's own calls (`CallResumeQ.resumeQW`), so it holds at every
pause; at a nested activation `RB.G ⊇ RA.FK` (`FrameDisj.Nested`: `RB.G = RA.FK`).

* `gkeep_of_q`: `Q` at a run configuration keeps `R.G`;
* `RetC R ra r₀ y`: **the return contract of an activation relative to its own entry** — `y` at
  the return address, no error, `sp` as at entry, the kept addresses `R.G` as at entry, x29 as at
  entry (Cranelift's epilogue reloads it with fp/lr), the callee-saved registers (up to `ckeep`)
  the checker's entry values `r₀`;
* **`retC_of_retEnd`**: `RetC` after the epilogue from `CallRetsEnd.RetEnd` at a `rets` pause;
* **`resume_premises_of_retC`**: the caller's resume premises (those of
  `resume_premises_of_retEnd`, with `hmr` derived) from `RetC` of a callee whose ABI entry state
  is the caller's state at its call but in the pc and `x30`, whose kept addresses contain the
  caller's `RA.FK`, and whose checker entry values are the registers after its prologue.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot VCodeThread Backend Backend.Proof AllocThread ThreadRefine
  E2E CallRetsEnd CallRetResume

/-- **`Q` at a run configuration keeps the kept addresses** (`StRel.gkeep`). -/
theorem gkeep_of_q {R : RL} {s : ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩)) : ∀ a, R.G a → s.mem a = R.s0.mem a :=
  (q_stRel hq).gkeep

/-- **The return contract of an activation relative to its entry** (module doc). -/
def RetC (R : RL) (ra : BitVec 64) (r₀ : Reg → CV) (y : ArmState) : Prop :=
  Arm.r .PC y = ra ∧ Arm.r .ERR y = .None ∧ spv y = spv R.s0 ∧
    (∀ a, R.G a → y.mem a = R.s0.mem a) ∧ xreg 29 y = xreg 29 R.s0 ∧
    ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (r₀ r)

/-- **`RetC` after the epilogue of a `rets` pause** (module doc). -/
theorem retC_of_retEnd {R : RL} {ra : BitVec 64} {env : Clif.Env} {p : Clif.Program}
    {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {r₀ : Reg → CV} {x : ArmState}
    {s' : Clif.State} (hret : RetEnd R ra env p MR slots r₀ x s') :
    ∃ n, (∀ i < n, R.GoodX (iterN R.step i x)) ∧ RetC R ra r₀ (iterN R.step n x) := by
  obtain ⟨b, k, allocs, its, m, w, -, -, -, -, -, -, n, hq, -, -, -, -, -, -, -, hgood, hpc, herr,
    hsp, hmem, ⟨-, hx29⟩, hcs, -⟩ := hret
  obtain ⟨mt, hq'⟩ := qa_q hq
  exact ⟨n, hgood, hpc, herr, hsp, fun a ha => by rw [hmem]; exact gkeep_of_q hq' a ha, hx29, hcs⟩

/-- **The caller's resume premises from the callee's return contract** (module doc): the state
`y` after the callee's return satisfies the premises of `CallRetResume.resume_layersR` other
than the program (which the linked machine restores). -/
theorem resume_premises_of_retC {RA RB : RL} (hRA : RA.Wf) (hRB : RB.Wf) {ra : BitVec 64}
    (hent : AbiCall RB.fb RB.base ra RB.s0) {r₀ : Reg → CV} {y : ArmState}
    (hy : RetC RB ra r₀ y) {x : ArmState} {m : Loc → CV} {w : ArmState} (hst : StRel RA x m w)
    (hfx : ∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x)
    (hlr : xreg 30 RB.s0 = Arm.r .PC x + 4#64)
    (hm0 : ∀ a, RA.FK a → RB.s0.mem a = x.mem a) (hG : ∀ a, RA.FK a → RB.G a)
    (hr₀ : ∀ r ∈ calleeSaved, ckeep r (r₀ r) =
      ckeep r (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize RB.af.isCaller).length RB.s0) (.reg r)))
    {info : CallInfo} {ops : Array Operand} {allocs : Array Loc}
    (hdef : ∀ d ∈ info.defs, ∃ q ∈ defPairs ops allocs, q.1.isLate = true ∧ q.2 = .reg d.1) :
    Arm.r .PC y = Arm.r .PC x + 4#64 ∧ Arm.r .ERR y = .None ∧ spOf y = spOf x ∧
      (∀ a, RA.FK a → y.mem a = x.mem a) ∧
      (∀ l, ValidLoc l → Live RA.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
        (∀ q ∈ defPairs ops allocs, q.1.isLate = true → q.2 ≠ l) →
        locVal RA.fr y l = locVal RA.fr x l) ∧
      (∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
        ckeep c (regVal y c) = ckeep c (regVal x c)) ∧
      xreg 29 y = xreg 29 x := by
  obtain ⟨hpc, herr, hsp, hmem, hx29, hcs⟩ := hy
  obtain ⟨he, hsp0, hra⟩ := entry_premises hRB hent hfx hlr
  have hcs' : ∀ r ∈ calleeSaved, ckeep r (regVal y r) = ckeep r (regVal x r) :=
    fun r hr => (hcs r hr).trans ((hr₀ r hr).trans (he r hr))
  have hsp' : spOf y = spOf x := hsp.trans hsp0
  have hmem' : ∀ a, RA.FK a → y.mem a = x.mem a := fun a ha =>
    (hmem a (hG a ha)).trans (hm0 a ha)
  exact ⟨hpc.trans hra, herr, hsp', hmem', hpresR_of_callee hRA hst hdef hcs' hsp' hmem',
    hkeep_of_callee hcs', hx29.trans (hfx (.GPR 29#5) (by simp) (by simp))⟩

end Concurrency.ArmAllocThread

import FV.Concurrency.CallRetResume
import FV.Concurrency.CallResumeWitness

/-!
# Witness: the caller resumed after a callee that returns a result (#473, step (1))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`) at its `bl` (`sBF`), a callee
that returns `42` in `x0` (`yX`: `x0 := 42`, the pc after the `bl`). `x0` is the call's result
register, not a clobber, so `CallResumeL.mstep_call`'s preservation premise fails for `yX`
(`not_hpres_yX`); **`resume_RX`**: `CallRetResume.mstep_callR`, its premise from
`hpresR_of_callee`, steps the allocated `call` to a store related by `Q` to `yX`.

Checks by `native_decide`/`decide` (witness only).
-/

namespace Concurrency.CallRetResume.Witness

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread AllocThread
  ArmAllocThread E2E IselResume CallSeg CallSeg.WitnessC CallResumeL CallResumeL.Witness

/-- **A callee's return with result `42` in `x0`.** -/
noncomputable def yX : ArmState := Arm.w (.GPR 0#5) 42#64 yR

theorem defsC1 : ∀ d ∈ infoC1.defs, ∃ q ∈ defPairs opsC1 #[.reg (.x 0), .reg (.x 0)],
    q.1.isLate = true ∧ q.2 = .reg d.1 := by
  native_decide

theorem defsC1_x0 : ∃ d ∈ infoC1.defs, d.1 = .x 0 := by native_decide

theorem calleeSaved_field : ∀ r ∈ calleeSaved, r.field ≠ some (.GPR 0#5) := by decide

theorem regVal_yX {r : Reg} (hr : r ∈ calleeSaved) : regVal yX r = regVal sBF r := by
  unfold yX yR
  rw [regVal_w (calleeSaved_field r hr), regVal_w_pc]

theorem spOf_yX : spOf yX = spOf sBF := by
  simp only [yX, yR, spOf, r_of_w_different (show StateField.GPR 31#5 ≠ .GPR 0#5 by decide),
    r_of_w_different (show StateField.GPR 31#5 ≠ .PC by simp)]

theorem mem_yX : yX.mem = sBF.mem := by
  unfold yX yR; rw [ArmFoot.w_mem, ArmFoot.w_mem]

/-- `mstep_call`'s premise fails for `yX`: `x0`, the call's result, is not clobbered but changed. -/
theorem not_hpres_yX (h0 : regVal sBF (.x 0) ≠ regVal yX (.x 0)) :
    ¬ ∀ l, ValidLoc l → Live RC.rf l →
      (∀ c ∈ (MInst.call infoC1).clobbers, l ≠ .reg c) → locVal RC.fr yX l = locVal RC.fr sBF l := by
  intro h
  obtain ⟨d, hd, hd0⟩ := defsC1_x0
  refine h0 (h (.reg (.x 0)) (fun r e => by cases e; decide) trivial (fun c hc e => ?_)).symm
  cases e
  have := (List.mem_filter.mp hc).2
  simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
  exact this d hd hd0

/-- **The caller's layer 4 after a callee returning a result** (module doc). -/
theorem resume_RX : ∃ (m m' : Loc → CV) (its : List RItem),
    Q RC sBF (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩) ∧
    MStep RC.vc (csem RC.F RC.ctx (xcallX VCodeThread.Witness.X0
        ((defPairs opsC1 #[.reg (.x 0), .reg (.x 0)]).map fun p => locVal RC.fr yX p.2) yX))
      ckeep RC.rf (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩)
      (.run ⟨0, its, m', yX⟩) ∧
    Q RC yX (.run ⟨0, its, m', yX⟩) := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  rw [checksPost.2.1] at hq
  obtain ⟨hi, hops, hsz⟩ := callChecksC
  have hk : 1 + 1 < (vcpC.blocks[0]!).insts.size := by rw [← checksPost.2.2.2.2]; decide
  have hcs : ∀ r ∈ calleeSaved, ckeep r (regVal yX r) = ckeep r (regVal sBF r) :=
    fun r hr => by rw [regVal_yX hr]
  have hmem : ∀ a, RC.FK a → yX.mem a = sBF.mem a := fun a _ => by rw [mem_yX]
  obtain ⟨m', hms, hst'⟩ := mstep_callR hq vb0C hi hk hops hsz
    (hpresR_of_callee wfRC (q_stRel hq) defsC1 hcs spOf_yX hmem) (hkeep_of_callee hcs)
    VCodeThread.Witness.X0 yX
  refine ⟨m, m', _, hq, hms, resumeQW wfRC hq vb0C hi ?_ ?_ spOf_yX hmem ?_ ?_ hst'
    (SameWorld.refl _ _)⟩
  · simp [yX, yR, r_of_w_different]
  · unfold yX yR
    rw [r_of_w_different (by simp), r_of_w_different (by simp)]
    exact (q_stRel hq).err
  · unfold yX; rw [w_program]; exact w_program
  · unfold yX yR E2E.xreg
    rw [r_of_w_different (by simp), r_of_w_different (by simp)]

end Concurrency.CallRetResume.Witness

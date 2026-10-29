import FV.Concurrency.CallRetPremises
import FV.Concurrency.CallRetResumeWitness

/-!
# Witness: the resume premises from the call and the callee's return (#473, step (1))

On the compiled caller of `atomic_load` (`CallSeg.WitnessC.RC`): `defsC1_q` (`hdef_of_q` at its
`call` item: the result register `x0` is a late def operand's location), `locsC1` (the def
locations are `[x0]`), `prefixHold_RX` (`prefixHold_outs` for the callee `yX` returning in
`x0`), `relW_id` (`relW_after_callee` for a callee leaving the memory as it was) and
`rets_RC` (`realized_rets` on the caller's own epilogue after the callee's return).

Checks by `native_decide`/`decide` (witness only).
-/

namespace Concurrency.CallRetResume.Witness

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread AllocThread
  ArmAllocThread E2E IselResume CallSeg CallSeg.WitnessC CallResumeL CallResumeL.Witness

theorem defsC1_eq : infoC1.defs = [(.x 0, .vreg 2 .int)] := by native_decide

theorem virtC1 : ∀ d ∈ infoC1.defs, ∃ n c, d.2 = .vreg n c := by
  rw [defsC1_eq]; intro d hd; simp at hd; subst hd; exact ⟨2, .int, rfl⟩

theorem qC1 : ∃ m its, Q RC sBF (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩) := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  rw [checksPost.2.1] at hq
  exact ⟨m, _, hq⟩

/-- **`hdef` of the caller's `call` from `Q`** (`hdef_of_q`). -/
theorem defsC1_q : ∀ d ∈ infoC1.defs, ∃ q ∈ defPairs opsC1 #[.reg (.x 0), .reg (.x 0)],
    q.1.isLate = true ∧ q.2 = .reg d.1 := by
  obtain ⟨m, its, hq⟩ := qC1
  exact hdef_of_q hq vb0C callChecksC.1 virtC1 callChecksC.2.1

/-- **The caller's def locations** (`defPairs_locs` through `Q`'s static check). -/
theorem locsC1 : (defPairs opsC1 #[.reg (.x 0), .reg (.x 0)]).map (·.2) =
    infoC1.defs.map (fun d => Loc.reg d.1) := by
  obtain ⟨m, its, hq⟩ := qC1
  obtain ⟨-, -, -, regs, -, -, -, -, -, -, -, -, -, -, cc, wh, ops', he, -, -, -, -, hops', hstat,
    -⟩ := q_op wfRC hq vb0C callChecksC.1 (ArmAllocThread.lt_size_of_not_term wfRC vb0C callChecksC.1 rfl)
  rw [callChecksC.2.1] at hops'
  cases hops'
  rw [he]
  exact defPairs_locs virtC1 callChecksC.2.1 hstat

theorem defsC1_x0' : ∀ (j : Nat) (d : Reg × Reg), infoC1.defs[j]? = some d →
    ∃ v, [(Reg.x 0, Reg.x 0)][j]? = some (v, d.1) := by
  rw [defsC1_eq]
  intro j d hd
  match j, hd with
  | 0, hd => simp at hd; subst hd; exact ⟨.x 0, rfl⟩

theorem defsC1_len : infoC1.defs.length = 1 := by rw [defsC1_eq]; rfl

/-- **`PrefixHold` of the call's outputs after the callee `yX`** (`prefixHold_outs`): the value
the callee returns in `x0`. -/
theorem prefixHold_RX :
    PrefixHold [⟨.i64, (regVal yX (.x 0)).setWidth 64⟩]
      ((defPairs opsC1 #[.reg (.x 0), .reg (.x 0)]).map fun p => locVal RC.fr yX p.2) := by
  obtain ⟨m, its, hq⟩ := qC1
  obtain ⟨-, -, -, regs, -, -, -, -, -, -, -, -, -, -, cc, wh, ops', he, -, -, -, -, hops', hstat,
    -⟩ := q_op wfRC hq vb0C callChecksC.1 (ArmAllocThread.lt_size_of_not_term wfRC vb0C callChecksC.1 rfl)
  rw [callChecksC.2.1] at hops'
  cases hops'
  rw [he]
  refine prefixHold_outs virtC1 callChecksC.2.1 hstat RC.fr (ys := [regVal yX (.x 0)])
    (us := [(.x 0, .x 0)]) ⟨by simp, fun j v x hv hx => ?_⟩ (fun j v q u hu hy => ?_)
    defsC1_x0' (by rw [defsC1_len]; simp)
  · match j, hv, hx with
    | 0, hv, hx => simp at hv hx; subst hv hx; rfl
  · match j, hu, hy with
    | 0, hu, hy => simp at hu hy; obtain ⟨-, rfl⟩ := hu; exact hy

/-- **The memory relation after a callee that leaves memory as it was** (`relW_after_callee`). -/
theorem relW_id {Γ : E2E.Rel} {f : Clif.Function} {c : BitVec 64}
    {slots : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : ArmState}
    (h : RelW Γ f c slots cm w) : RelW Γ f c slots ((cm.free []).leave) w :=
  relW_after_callee h h.1.1 (fun a n hv => by simpa [Clif.Mem.free, Clif.Mem.valid] using hv) (fun _ _ => rfl)
    rfl h.2.2

/-- **The caller's epilogue after the callee's return, as a private segment** (`realized_rets`
on `CallSeg.WitnessC.callerPost`'s state at the caller's `rets`). -/
theorem rets_RC {y : ArmState} (hy : PostA sBF y) :
    ∃ s n, 0 < n ∧ Arm.r .PC (iterN RC.step n s) = 0x4000#64 ∧
      ∀ {L : List Lab} {mon : Mon} {t' : ArmState × Mon}, L.length < n →
        PRun Policy.arm RC.step (OkPriv RC) (s, mon) L t' → t'.1 = iterN RC.step L.length s := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  obtain ⟨hpc, herr, hsp, hmem, hprog, hfp⟩ := hy
  obtain ⟨info, hinfo⟩ := callC1
  have hstr := q_stRel hq
  rw [checksPost.2.1] at hq
  have hq1 := resumeQ wfRC hq vb0C hinfo hpc herr hsp hmem (hprog.trans hstr.prog.symm) hfp
  have hA1 : AInv RC (.run ⟨0, (postMv (.x 0)).map (fun p => RItem.move p.1 p.2) ++
      [.op 2 #[.reg (.x 0)]], locVal RC.fr y, y⟩) := by
    intro _ ⟨a, ha⟩
    simp [postMv, RealizeCompiled.Witness.savesL] at ha
  obtain ⟨n1, hqa2, -⟩ := moves_privQA wfRC (postMv (.x 0)) _ _ _ (.inl ⟨hq1, hA1⟩)
    (moves_noRet (R := RC) postMvC_noRet)
  obtain ⟨mt2, hq2⟩ := qa_q hqa2
  obtain ⟨n, hn0, hpc', -, -, -, -, hr⟩ :=
    realized_rets wfRC abiRC (g := RC.step) (fun _ _ _ => rfl) hq2 vb0C instC2
  exact ⟨_, n, hn0, hpc', fun hlt hp => (hr hlt hp).1⟩

end Concurrency.CallRetResume.Witness

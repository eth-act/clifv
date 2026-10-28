import FV.E2E.IselSimITry
import FV.E2E.NonVacuityLink

/-!
# Non-vacuity of the counted CLIF → VCode simulation (SEM1, `docs/plans/uninit.md` §5.9)

* `step_only_ret`: restricting the environment to the (empty) invocation of a `return` step
  does not change it (`Clif.step_only`);
* `a2_iselSimI`: `iselSim_relWI` applies to the witness program's compiled function `a2`
  (`LinkWitness`), every function-level premise discharged (`InstCallsOne`/`TryCallsOne` from
  its code: no call statement, no `try_call`; the callee contracts vacuous: no externs, no
  indirect call), the entry premises remaining.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- A `return` state: its step makes no extern invocation. -/
theorem step_only_ret (env : Clif.Env) (p : Clif.Program) (s : Clif.State)
    (hb : s.frame.body = []) (ht : s.frame.term = .ret []) :
    Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
  Clif.step_only fun _ _ _ ⟨_, h⟩ => by simp [hb, ht] at h

/-- `a2` has no `call`/`call_indirect` statement. -/
theorem a2_noCallStmt : fA2.blocks.all (fun B => B.body.all fun st => !st.inst.isCallLike) = true := by
  native_decide

/-- **`iselSim_relWI` applies** to the program's compiled function `a2` (the entry premises
remain). -/
theorem a2_iselSimI {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV) (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ us outs w, VRetFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩
          (ExtSemI.const Xb)) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w.1) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      VTrapFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩ (ExtSemI.const Xb))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hfa := facts hA2
  have hcompiled : Compiled fA2 (A fA2).k (A fA2).vc (A fA2).vcp (A fA2).rf
      (A fA2).af (A fA2).fa (A fA2).fb := by
    obtain ⟨hl, hp, ha, he, hla, hk, hb⟩ := pipe_spec hfa.pipe
    exact ⟨hl, hfa.lowerOk, hp, hfa.prepOk, hfa.check, ha, he, hla⟩
  have ha := a2B_true
  simp only [a2B, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨he9, heA⟩, hi9⟩, hiA⟩, hnt⟩, hnc⟩, hchk⟩ := ha
  have hns := a2_noCallStmt
  simp only [List.all_eq_true, Bool.not_eq_true'] at hns
  have hone : InstCallsOne fA2 := by
    intro _ _ _ inst _ _ _ _ _ ⟨B, hB, stm, hstm, hi⟩ _ _ _ _ _ _ _ hcl
    rw [← hi, hns B hB stm hstm] at hcl
    cases hcl
  have htc : TryCallsOne fA2 :=
    ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => absurd ht (by
        intro h; have := hnt B hB; rw [h] at this; cases this),
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => absurd ht (by
        intro h; have := hnt B hB; rw [h] at this; cases this)⟩
  exact iselSim_relWI (hL.subset fA2 hA2) hcompiled hone htc
    (fun _ _ _ => ⟨fun ext hin => by simp [heA] at hin,
      by rw [indSigs_nil_of_indFree (indFreeB_sound hiA)]; exact xCallsIndOk_nil _ _ _⟩)
    (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr fuel

end E2E.LinkWitness

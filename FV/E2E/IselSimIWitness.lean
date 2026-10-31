import FV.E2E.BackendWorldI
import FV.E2E.NonVacuityLink

/-!
# Non-vacuity of the counted CLIF → VCode simulation and pipeline (SEM1, `docs/plans/uninit.md` §5.9)

* `step_only_ret`: restricting the environment to the (empty) invocation of a `return` step
  does not change it (`Clif.step_only`);
* `a2_callsOne`, `a2_compiled`, `a2_xcalls`: the function-level premises for the witness
  program's compiled function `a2` (`LinkWitness`: no call statement, no `try_call`, no externs,
  no indirect call);
* `a2_iselSimI`: `iselSim_relWI` applies to `a2`; `a2_worldPRI`: `backend_correct_worldPRI`
  applies to `a2` (the entry premises remain).
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

/-- `a2`'s call counts: no call statement, no `try_call`. -/
theorem a2_callsOne : InstCallsOne fA2 ∧ TryCallsOne fA2 := by
  have ha := a2B_true
  simp only [a2B, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hnt⟩, -⟩, -⟩ := ha
  have hns := a2_noCallStmt
  simp only [List.all_eq_true, Bool.not_eq_true'] at hns
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => absurd ht (by
        intro h; have := hnt B hB; rw [h] at this; cases this),
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨B, hB, ht⟩ => absurd ht (by
        intro h; have := hnt B hB; rw [h] at this; cases this)⟩
  intro _ _ _ inst _ _ _ _ _ ⟨B, hB, stm, hstm, hi⟩ _ _ _ _ _ _ _ hcl
  rw [← hi, hns B hB stm hstm] at hcl
  cases hcl

theorem a2_compiled : Compiled fA2 (A fA2).k (A fA2).vc (A fA2).vcp (A fA2).rf
    (A fA2).af (A fA2).fa (A fA2).fb := by
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hfa := facts hA2
  obtain ⟨hl, hp, ha, he, hla, hk, hb⟩ := pipe_spec hfa.pipe
  exact ⟨hl, hfa.lowerOk, hp, hfa.prepOk, hfa.check, ha, he, hla⟩

/-- `a2`'s callee contracts (it has no externs and no indirect call), at every index. -/
theorem a2_xcalls (env' : Clif.Env) (MR : MemRelT) (XI : ExtSemI) (n : Nat) :
    XCallsOk env' (fA2.externs.map (·.2)) MR (XI.at n) ∧
      XCallsIndOk env' (indSigs fA2) MR (XI.at n) := by
  have ha := a2B_true
  simp only [a2B, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.not_eq_true'] at ha
  obtain ⟨⟨⟨⟨⟨⟨-, heA⟩, -⟩, hiA⟩, -⟩, -⟩, -⟩ := ha
  exact ⟨fun ext hin => by simp [heA] at hin,
    by rw [indSigs_nil_of_indFree (indFreeB_sound hiA)]; exact xCallsIndOk_nil _ _ _⟩

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
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w.1) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      VTrapFrom (A fA2).vc (csemI F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩ (ExtSemI.const Xb))
        ⟨0, 0, ρ₀, (w₀, 0)⟩ c') := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact iselSim_relWI (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl ρ₀ hce hrel hargs htr fuel

/-- **`backend_correct_worldPRI` applies** to the program's compiled function `a2` (the entry
premises remain): one counted VCode outcome per returning CLIF run, realised by every
`ActEntryPR` activation. -/
theorem a2_worldPRI {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F (fun _ => none) cm w ∧ (A fA2).vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
            (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s) ∧
            PostTrace (A fA2).fa (A fA2).af base (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) s n) ∧
    (∀ c', Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
        (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
        ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
          (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
        ∃ n, TrapAt (A fA2).fb base c' (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s)) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact backend_correct_worldPRI (hL.subset fA2 hA2) a2_compiled a2_callsOne.1 a2_callsOne.2
    (hL.covered fA2 hA2) (fun _ n _ => a2_xcalls _ _ _ n) (fun n b h => by cases h) rfl hce hrel
    hargs htr fuel

end E2E.LinkWitness

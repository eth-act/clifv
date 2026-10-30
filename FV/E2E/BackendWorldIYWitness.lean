import FV.E2E.BackendWorldIY
import FV.E2E.IselSimIWitness

/-!
# Witness for the guarded world reads (SEM1 #537, item (2), `FV/E2E/BackendWorldIY.lean`)

`a2_worldPRIY`: `backend_correct_worldPRIY` applies to `LinkWitness`'s compiled function `a2`,
with the guard `Ok w Y := Y = F` (where the guarded semantics is `csemVI`, `csemVIG_eqF`, so the
premise `hGd` holds): the activations realising the returning run have their world reads guarded
(`actWReadsIn`).
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_worldPRIY` applies** to the program's compiled function `a2` (the entry
premises remain). -/
theorem a2_worldPRIY {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (Kp : Nat) (cc : BitVec 64)
          (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState) (s : Arm.ArmState),
          ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
            (ExtSemI.const Xb) H base ra Kp cc P R s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) n s) ∧
            ∀ i < n, actWReadsIn (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb base s
              ((ExtSemI.const Xb).at 0) H K G (GotV (A fA2).vcp) (fun _ Y => Y = F)
              (runX (ArmStepX ((ExtSemI.const Xb).at 0) H (A fA2).fa) i s) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  intro vals cm hrun
  obtain ⟨us, outs, w, -, -, -, -, -, h⟩ := (backend_correct_worldPRIY (hL.subset fA2 hA2) a2_compiled
    a2_callsOne.1 a2_callsOne.2 (hL.covered fA2 hA2) (fun _ n _ => a2_xcalls _ _ _ n)
    (fun n b h => by cases h) rfl hce hrel hargs htr fuel (fun _ Y => Y = F)
    (fun us outs w nc h => by rw [csemVIG_eqF]; exact h)).1 vals cm hrun
  refine ⟨us, outs, w, fun H G base ra Kp cc P R s he => ?_⟩
  obtain ⟨n, h1, -, h3⟩ := h H G base ra Kp cc P R s he
  exact ⟨n, h1, h3⟩

end E2E.LinkWitness

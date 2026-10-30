import FV.E2E.BackendTwoRunLR
import FV.E2E.BackendTwoRunWitness
import FV.E2E.LinkArmX30CheckWitness

/-!
# Witnesses for the machine lock from the entries to the return (SEM1 #537, `BackendTwoRunLR.lean`)

* `frLine_lines_jump`: `frLine_lines` at a concrete instruction;
* `a2_twoRunLER`: `backend_twoRunLER` (and so `backend_twoRunLEF`, `RL.retAgreeX_rets`) applies to
  `LinkWitness`'s compiled function `a2`, one activation entered twice with the hooks that change
  nothing (the `x30` check by `x30Free_all`, `hcall`/`htls` by `hookNIX_id`-style identity hooks);
* `hookNIX_id_call`: `stEqOutX_call_of_hookNIX` on the identity hooks.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

theorem frLine_lines_jump :
    ∀ x t, Line.ins x t ∈ [Line.ins (.b (.block 3)) none] → x.frLine = false :=
  frLine_lines (c := ⟨0, 0⟩) (m := .jump 3) (ps := {}) (ps' := {}) rfl

/-- The identity hooks. -/
def idHooks : ArmHooks := ⟨fun _ s => s, fun _ _ s => s⟩

/-- **`backend_twoRunLER` applies** to `a2`, one activation entered twice with the identity hooks:
the lock along the body and `RetAgreeX` at the return. -/
theorem a2_twoRunLER {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat)
    {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {Pp : Nat → BitVec 64 → BitVec 8} {Rr : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
      (ExtSemI.const Xb) idHooks base ra Kp cc Pp Rr s w₀) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ N, RetAgreeX (frameDrop (A fA2).af + K) (spv s)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize).length + N +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s)
        (iterN (ArmStepX Xb idHooks (A fA2).fa)
          ((prologueLines (A fA2).af.saves (A fA2).af.frameSize).length + N +
            ((epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1)) s) := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hc := a2_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨p, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  have hx30 : (A fA2).fa.x30Free lm = true := by
    have h := List.all_eq_true.mp x30Free_all fA2 hA2
    rwa [show getOk (labelOffsets (A fA2).fa.lines) = lm by rw [hlm]; rfl] at h
  intro vals cm hrun
  obtain ⟨N, -, -, -, h⟩ := backend_twoRunLER (D := fun _ => False)
    (hL.subset fA2 hA2) hc
    a2_callsOne.1 a2_callsOne.2 (fun _ n _ => a2_xcalls _ _ _ n) (fun _ _ _ => xb_xNI)
    (fun _ => xbTls F) (fun n b h => by cases h) rfl (fun _ => 0) hce hrel hrel hargs
    (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel hlm ⟨p, hk ▸ hpsF, rfl⟩ he he
    rfl (hL.covered fA2 hA2) hx30
    (fun _ _ _ _ _ _ _ _ _ _ _ hl _ _ => hl) (fun _ _ _ _ _ _ _ _ _ _ _ hl _ _ _ => hl)
    ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩ rfl vals cm hrun
  exact ⟨N, h⟩

/-- `stEqOutX_call_of_hookNIX` on the identity hooks. -/
theorem hookNIX_id_call {R : RL} {c c' : MConf CV Arm.ArmState}
    (hW : ∀ a, MConf.WDiff c c' a → R.F a) {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc c c') u u') :
    StEqOutX (R.Zc c c') (idHooks.call none u) (idHooks.call none u') :=
  stEqOutX_call_of_hookNIX (BD := fun _ => True) (hookNIX_id _ _) hW trivial h

end E2E.LinkWitness

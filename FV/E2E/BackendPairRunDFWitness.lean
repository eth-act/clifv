import FV.E2E.BackendPairRunDF
import FV.E2E.BackendTwoRunWitness

/-!
# Witness for the paired run from non-interference at the exterior (SEM1 #537, #713,
`BackendPairRunDF.lean`)

* `a2_pairRunDF`: `backend_pairRunDF` applies to `LinkWitness`'s compiled function `a2` (which
  calls externs), the external semantics' non-interference only at `F` (`XNI.xnif` of the
  witness extern's `XNI`), with the world difference `D := F` (inside `F`).
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_pairRunDF` applies** to `a2`, non-interference at `F` only. -/
theorem a2_pairRunDF {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ us outs w,
        VRetFrom (A fA2).vcp (pairDI (csemV (GotV (A fA2).vcp) F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩)
          F ⟨(A fA2).fa.k, (A fA2).af.slotBase⟩ (ExtSemI.const Xb))
          ⟨0, 0, fun _ => 0, ((w₀, w₀), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ F b) w.1.1 w.1.2 := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  exact backend_pairRunDF (D := F) (XI := ExtSemI.const Xb) (hL.subset fA2 hA2) a2_compiled
    a2_callsOne.1 a2_callsOne.2 (fun _ n _ => a2_xcalls _ _ _ n) (fun _ _ _ => XNI.xnif xb_xNI)
    (fun _ => xbTls F) (fun n b h => by cases h) rfl (fun _ h => h) (fun _ => 0) hce hrel hrel
    hargs (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel

end E2E.LinkWitness

import FV.E2E.BackendTwoRun
import FV.E2E.IselSimIWitness

/-!
# Witness for two activations along one CLIF run (SEM1 #537, item (3), `BackendTwoRun.lean`)

`a2_twoRunPRIY`: `backend_twoRunPRIY` applies to `LinkWitness`'s compiled function `a2` (the
base externs answer no call, so their non-interference is vacuous; `xbTls`), with the guard
`Ok w Y := Y = F` (`csemVG_eqF`: the paired guarded semantics is the unguarded one, so `hGdP`
holds) and the lock "equal states" for one activation entered twice: the two machine runs agree
at every index and both return.
-/

namespace E2E.LinkWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- The base externs answer no call: their non-interference is vacuous. -/
theorem xb_xNI {F : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} :
    XNI F syms exts sigs sp0 Lg Xb := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  cases h

/-- **`backend_twoRunPRIY` applies** to the program's compiled function `a2` (the entry
premises remain), for one activation entered twice: the two runs agree at every index and
return to `ra`. -/
theorem a2_twoRunPRIY {F : BitVec 64 → Prop} {c : BitVec 64} {K : Nat} {args : List Clif.Val}
    {cs : Clif.State} {w₀ : Arm.ArmState} (hce : ClifEntry fA2 args cs)
    (hrel : RelW ⟨F, fun _ => none, (A fA2).af.slotBase,
      (RAFrame.compute (A fA2).vcp (A fA2).rf).intBase⟩ fA2 c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F fA2.sig args w₀)
    (htr : TrapsExplicit Clif.Rust.env (L F).P.bare cs) (fuel : Nat)
    {H : ArmHooks} {G : BitVec 64 → Prop} {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64}
    {Pp : Nat → BitVec 64 → BitVec 8} {Rr : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPR (A fA2).vcp (A fA2).rf (A fA2).af (A fA2).fa (A fA2).fb K F G
      (ExtSemI.const Xb) H base ra Kp cc Pp Rr s w₀) :
    ∀ vals cm, Clif.runLoop Clif.Rust.env (L F).P.bare fuel cs = .returned vals cm →
      ∃ N, Arm.r .PC (iterN (ArmStepX Xb H (A fA2).fa)
        ((prologueLines (A fA2).af.saves (A fA2).af.frameSize (A fA2).af.isCaller).length + N +
          (epiLines (A fA2).af.saves (A fA2).af.frameSize).length + 1) s) = ra := by
  have hL := L_ok (fun _ => True) (fun _ _ => trivial)
  have hA2 : fA2 ∈ P.funcs := by simp [P]
  have hc := a2_compiled
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  obtain ⟨body, psF, hpsF, -, hk⟩ := emitFunc_ok hc.emit
  intro vals cm hrun
  obtain ⟨N, -, -, -, -, -, -, hpc, -⟩ := backend_twoRunPRIY (D := fun _ => False) (hL.subset fA2 hA2) hc
    a2_callsOne.1 a2_callsOne.2 (fun _ n _ => a2_xcalls _ _ _ n) (fun _ _ _ => xb_xNI)
    (fun _ => xbTls F) (fun n b h => by cases h) rfl (fun _ => 0) hce hrel hrel hargs
    (SameWorld.refl _ _) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) htr fuel (fun _ Y => Y = F)
    (fun us outs w h => by simpa only [csemVG_eqF] using h) hlm (hk ▸ hpsF) he he rfl
    (hL.covered fA2 hA2) (fun _ _ => True) (fun _ _ u u' => u = u') (fun _ _ => fun _ Y => Y = F)
    (fun _ _ => fun _ Y => Y = F) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun _ _ _ u u' => u = u') (fun _ _ _ _ _ h => h ▸ rfl) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ _ _ h => h ▸ rfl) (fun _ _ _ _ _ _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) rfl vals cm hrun
  exact ⟨N, hpc⟩

end E2E.LinkWitness

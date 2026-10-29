import FV.E2E.LinkArmProgCallP
import FV.E2E.LinkArmProphDetEWitness

/-!
# Witnesses for `progCallP` (`FV/E2E/LinkArmProgCallP.lean`)

* `progCallP_Lu`: `progCallP` on `LinkArmProphDetWitness.Lu` (a program with a call) with its
  induction hypothesis discharged by `thmPDE_LU`: a call `f → h` from any world with the premises
  of `progCall` has an outcome realised from the canonical state (`canon_agree`).
-/

namespace E2E.LinkArmProgCallPWitness

open Backend Backend.Proof LinkArmProphDetWitness LinkArmProphDetEWitness

/-- `progCallP` on `Lu` at depth `M + 1`, realised from the canonical state. -/
theorem progCallP_Lu (M : Nat) {n : String} {h : Clif.Function} (hpf : Lu.P.func? n = some h)
    (hcal : ∃ g ∈ Lu.P.funcs, Lu.Callee g h)
    (hib : ((RAFrame.compute (Lu.A h).vcp (Lu.A h).rf).intBase = 0 ∧
      (RAFrame.compute (Lu.A h).vcp (Lu.A h).rf).size = (Lu.A h).af.frameSize - clobberBytes (Lu.A h).af.saves) ∨ Lu.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, Lu.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (Lu.A h).af + Lu.K M ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (Lu.A h).af + Lu.K M) (spv w) a → F a ∧ ¬ Lu.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F Lu.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : Lu.NeedSlots → Lu.PlaceAt cm (spv w))
    (hinit : Clif.initState Lu.P n vals cm = .ok cs)
    (hrun : Lu.crun (M + 1) cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (k : Nat),
      Lu.pcall (M + 1) h (Lu.canon h uses w) =
        Arm.set_program (runX (Lu.mach M h) k (enterAt (Lu.A h) (Lu.canon h uses w)))
          (Lu.canon h uses w).program ∧
      ActRet (Arm.r .PC (Lu.canon h uses w) + 4) F
        (fun a => F a ∧ ¬ StackBelow (frameDrop (Lu.A h).af + Lu.K M) (spv w) a)
        us outs wf (enterAt (Lu.A h) (Lu.canon h uses w))
        (runX (Lu.mach M h) k (enterAt (Lu.A h) (Lu.canon h uses w))) := by
  obtain ⟨hh, -⟩ := Clif.Program.func?_some hpf
  obtain ⟨us, outs, wf, -, -, -, -, -, hall, -⟩ :=
    Lu.progCallP (κ := fun M _ => Lu.K M) Lu_ok (M := M + 1) (Nat.succ_pos M) (thmPDE_LU M)
      hpf hcal hib himgF herr hal hroom hdead ((Lu.budget_K Lu_ok).2 _ h hh) hmr hargs hsav hpl
      hinit hrun
  obtain ⟨k, h1, h2⟩ := hall _ (Lu.callerOk_canon Lu_ok hh himgF uses w)
    (Lu.canon_agree (κ := fun M _ => Lu.K M) h uses w (M + 1)).1
    (Lu.canon_agree (κ := fun M _ => Lu.K M) h uses w (M + 1)).2
  exact ⟨us, outs, wf, k, h1, h2⟩

end E2E.LinkArmProgCallPWitness

import FV.E2E.LinkArmThmPRBR
import FV.E2E.LinkArmProgOsPRBR
import FV.E2E.LinkArmProgOsPWitness

/-!
# Witnesses for `ThmPRBR` and the calls on it (`FV/E2E/LinkArmThmPRBR.lean`,
`LinkArmProgCallPRBR.lean`, `LinkArmProgOsPRBR.lean`, `LinkArmDetTabPRB.lean`)

On `LinkArmProphDetWitness.Lu` (a program with a call `f → h`, no slots):
* `noSlots_Lu`: no program callee has slots; `thmPRBR_LU`: `ThmPRBR` at every depth
  (`thmPRBR_of_thm`); `thmPRB_toR_LU`: `ThmPRB.toR` applies to it.
* `progCallPRBR_Lu`, `progCallPRBR_at_Lu`, `calleeOkPRBR_Lu`, `calleeTryOkPRBR_Lu`: the call
  lemmas on `Lu` with the induction hypothesis discharged by `thmPRBR_LU`; the determinism
  premises `DetPRB`/`DetTabPRB` remain premises (to be discharged by `thmPDER_det_of`).
-/

namespace E2E.LinkArmThmPRBRWitness

open Backend Backend.Proof LinkArmProphDetWitness

/-- No function of `Lu` has stack slots. -/
theorem noSlots_Lu : ¬ Lu.NeedSlots := by
  rintro ⟨g, -, h, hc, hne⟩
  have hh := Lu.callee_mem hc
  change h ∈ [LinkArmUProgWitness.fF, LinkArmUProgWitness.fH] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl <;> exact hne (by native_decide)

/-- **`ThmPRBR` at every depth for a program with a call.** -/
theorem thmPRBR_LU (M : Nat) : Lu.ThmPRBR (fun M _ => Lu.K M) M :=
  Lu.thmPRBR_of_thm Lu_ok noSlots_Lu (Lu.thm Lu_ok (Lu.budget_K Lu_ok) M)

/-- `noRetAt_of` at a machine entry of `Lu` with a linked call's return address. -/
theorem noRetAt_Lu (M : Nat) {g : Clif.Function} (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop}
    {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (hME : Lu.MachEntry (fun M _ => Lu.K M) M g F G ra s w₀) (hra : RaOk (Lu.A g) (ra - 4))
    {n : Nat} (htr : PostTrace (Lu.A g).fa (Lu.A g).af (Lu.A g).base (Lu.mach M g) s n)
    (herr : Arm.r .ERR (runX (Lu.mach M g) n s) = .None) :
    ∀ j < n, ¬ Lu.RetAt g s (runX (Lu.mach M g) j s) :=
  Lu.noRetAt_of Lu_ok hg hME hra htr herr

/-- `ThmPRB.toR` on `Lu` (from any `ThmPRB`). -/
theorem thmPRB_toR_LU (M : Nat) (h : Lu.ThmPRB (fun M _ => Lu.K M) M) :
    Lu.ThmPRBR (fun M _ => Lu.K M) M :=
  LinkSys.ThmPRB.toR Lu h

/-- `progCallPRBR` on `Lu` at depth `M + 1` (the induction hypothesis by `thmPRBR_LU`). -/
theorem progCallPRBR_Lu (M : Nat) (hdet : Lu.DetPRB (fun M _ => Lu.K M) M) {n : String}
    {h : Clif.Function} (hpf : Lu.P.func? n = some h) (hcal : ∃ g ∈ Lu.P.funcs, Lu.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, Lu.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (Lu.A h).af + Lu.K M ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (Lu.A h).af + Lu.K M) (spv w) a → F a ∧ ¬ Lu.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F Lu.syms cm w)
    (hargs : ArgsAt h.sig vals uses w) (hsav : StackArgsAvoid F h.sig vals w)
    (htab : Lu.TableOf M h (enterAt (Lu.A h) (Lu.canon h uses w)) (LinkSys.calleeIni h ini))
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
  obtain ⟨us, outs, wf, _, -, -, -, -, -, -, hall⟩ :=
    Lu.progCallPRBR (κ := fun M _ => Lu.K M) Lu_ok (M := M + 1) (Nat.succ_pos M) (thmPRBR_LU M)
      hdet hpf hcal himgF herr hal hroom hdead hmr hargs hsav (fun hN => absurd hN noSlots_Lu)
      (fun hN => absurd hN noSlots_Lu) htab hinit hrun
  obtain ⟨k, hk, hret, -⟩ := hall _ (Lu.callerOk_canon Lu_ok hh himgF uses w)
    (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  exact ⟨us, outs, wf, k, hk, hret⟩

/-- `progCallPRBR_at` on `Lu` at depth `M + 1`, at the canonical state itself. -/
theorem progCallPRBR_at_Lu (M : Nat) (hdet : Lu.DetPRB (fun M _ => Lu.K M) M)
    (hdt : Lu.DetTabPRB (fun M _ => Lu.K M) (M + 1)) {n : String}
    {h : Clif.Function} (hpf : Lu.P.func? n = some h) (hcal : ∃ g ∈ Lu.P.funcs, Lu.Callee g h)
    {F : BitVec 64 → Prop} (himgF : ∀ a, Lu.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (Lu.A h).af + Lu.K M ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (Lu.A h).af + Lu.K M) (spv w) a → F a ∧ ¬ Lu.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} {ini : Clif.SlotInit} (hmr : MemRel F Lu.syms cm w)
    (hargs : ArgsAt h.sig vals uses w) (hsav : StackArgsAvoid F h.sig vals w)
    (htab : Lu.TableOf M h (enterAt (Lu.A h) (Lu.canon h uses w)) (LinkSys.calleeIni h ini))
    (hinit : Clif.initState Lu.P n vals cm = .ok cs)
    (hrun : Lu.crun (M + 1) cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState) (e : Nat),
      PrefixHold rvals outs ∧ MemRel F Lu.syms cm' wf := by
  obtain ⟨hh, -⟩ := Clif.Program.func?_some hpf
  obtain ⟨us, outs, wf, e, -, -, hhold, hmem, -⟩ :=
    Lu.progCallPRBR_at (κ := fun M _ => Lu.K M) Lu_ok (M := M + 1) (Nat.succ_pos M)
      (thmPRBR_LU M) hdet hdt hpf hcal himgF herr hal hroom hdead hmr hargs hsav
      (fun hN => absurd hN noSlots_Lu) (fun hN => absurd hN noSlots_Lu) hinit hrun
      (Lu.callerOk_canon Lu_ok hh himgF uses w) (fun _ _ _ _ => rfl) (fun _ _ => rfl) htab
  exact ⟨us, outs, wf, e, hhold, hmem⟩

/-- `calleeOkPRBR` on `Lu` (the induction hypothesis by `thmPRBR_LU`). -/
theorem calleeOkPRBR_Lu (M : Nat) (hdet : 0 < M → Lu.DetPRB (fun M _ => Lu.K M) (M - 1))
    {g : Clif.Function} (hg : g ∈ Lu.P.funcs) {F G : BitVec 64 → Prop}
    {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : Lu.MachEntry (fun M _ => Lu.K M) M g F G ra s w₀) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) (n : Nat) :
    CalleeOkGP (LinkArmProgOsPWitness.QR (Lu.K M) P R n) F (Lu.K M) G s
      (CallAt (Lu.A g).fa (Lu.A g).base)
      (Lu.XPRBT (fun M _ => Lu.K M) M g F P R n) (Lu.hooks M) (Lu.A g).vcp.CallSite
      (GotV (Lu.A g).vcp) :=
  Lu.calleeOkPRBR Lu_ok (Lu.budget_K Lu_ok) (fun _ => thmPRBR_LU _) hdet hg he fun _ hq _ => hq

end E2E.LinkArmThmPRBRWitness

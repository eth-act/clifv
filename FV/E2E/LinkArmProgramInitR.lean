import FV.E2E.LinkArmProgramInitEX
import FV.E2E.LinkArmTwinCE

/-!
# The linked program under the machine's own slot table, corrected determinism (SEM1 #537, #719, #716)

`backend_correct_program_core_initEX` / `backend_correct_program_initEX` take `DetPRB`, which is
false for real programs (#719). Here the corrected premise `DetPRBR` (#719, the canonical
activation's CLIF run returns) through `thmPRBRLE_allCR` / `thmPRBG_allCR`; `DetTabPRBE`,
`DetTabPRBr` come from the call twins `CallTwinCE` (#716) at the binary level (`InitOkR`).

* **`backend_correct_program_core_initEXR`**, **`backend_correct_program_initEXR`**: returning
  runs, with the per-state facts. The trapping counterpart is `backend_correct_program_initETR`
  (`LinkArmTrapE`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`backend_correct_program_core_initEX` with `DetPRBRU`** (module doc; #732), the oracle
route's premises only under `NeedSlots`. -/
theorem backend_correct_program_core_initEXRU (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.DetPRBRU κ M) (hdt : L.NeedSlots → ∀ M, L.DetTabPRBE κ M)
    (hdtr : L.NeedSlots → ∀ M, L.DetTabPRBr κ M) (hK : L.NeedSlots → L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.iniOf M f s))
    {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) ∧
      L.RunGoodL M f s := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK'⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntryB κ M f L.F args cs w₀ (L.iniOf M f s) := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_body hfr (entryRegs_of_check hc.lowerOk) hbe hargs (fun off v hm k hk hk' => ?_) hres
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_pipeline hc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB]; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB, hd]
      have := hent.spAligned
      have := L.frameSize_mod hL hf
      omega
  -- the machine side, with the run's own prophecies
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  have hMEP : L.MachEntryPR κ M f L.F L.Img ra s w₀
      (prophOf (L.mach M f) (L.A f).fa (L.A f).base s)
      (prophStOf (L.mach M f) (L.A f).fa (L.A f).base s) :=
    ⟨⟨hME, prophOk_prophOf _ _ _ _ _ _⟩, fun _ hcp _ _ _ _ => by rw [prophStOf_call hcp]⟩
  have hra : RaOk (L.A f) (ra - 4) := .inl fun k hk => by
    rw [BitVec.sub_add_cancel]; exact hent.raOutside k hk
  by_cases hN : L.NeedSlots
  · have htab := L.tableOfE_iniOf (M := M) hL (hK hN) hf hent.program
    obtain ⟨us, outs, wf, n, e, hus, hlen, hhold, hmemR, -, hret, -⟩ :=
      L.thmPRBRLE_allCRU hL hκ hN (hBR hN) (hRC hN) (hdet hN) (hdt hN) M f hf L.F args cs w₀ fuel
        vals cm (L.iniOf M f s) L.Img ra s hWE hMEP hra htab hrun
    exact ⟨armRefines_of_actRet hus hlen hhold hmemR hret,
      L.thmPRBG_allCRU hL hκ hN (hBR hN) (hRC hN) (hdet hN) (hdt hN) (hdtr hN) M f hf L.F args cs
        w₀ fuel vals cm (L.iniOf M f s) L.Img ra s hWE hMEP hra htab hrun⟩
  · obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall, -⟩ :=
      L.thm hL hκ M f hf L.F args cs w₀ fuel vals cm (hWE.toWorldEntry L hN) hrun
    obtain ⟨n, hret, -⟩ := hall L.Img ra s hME
    exact ⟨armRefines_of_actRet hus hlen hhold hmemR hret,
      (L.thmG hL hκ M f hf L.F args cs w₀ fuel vals cm (hWE.toWorldEntry L hN) hrun).1 L.Img ra s
        hMEP.entryP.entry⟩

/-- **`backend_correct_program_core_initEX` with `DetPRBR`** (`backend_correct_program_core_initEXRU`,
`DetPRBR.toU`). -/
theorem backend_correct_program_core_initEXR (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRBR κ M)
    (hdt : ∀ M, L.DetTabPRBE κ M) (hdtr : ∀ M, L.DetTabPRBr κ M) (hK : L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.iniOf M f s))
    {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) ∧
      L.RunGoodL M f s :=
  backend_correct_program_core_initEXRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L (hdet M)) (fun _ => hdt) (fun _ => hdtr) (fun _ => hK) hf M
    hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun

/-- **`backend_correct_program_initEX` with `DetPRBRU`** (#732): a returning whole-program CLIF
run of at most `M + 1` steps from `f`'s entry placed with the machine's own table is realised by
the linked machine of depth `M`, with the per-state facts; the oracle route's premises only under
`NeedSlots`. -/
theorem backend_correct_program_initEXRU (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.NeedSlots → L.BaseRetOk)
    (hRC : L.NeedSlots → ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : L.NeedSlots → ∀ M, L.std.DetPRBRU κ M) (hdt : L.NeedSlots → ∀ M, L.std.DetTabPRBE κ M)
    (hdtr : L.NeedSlots → ∀ M, L.std.DetTabPRBr κ M) (hK : L.NeedSlots → L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.std.iniOf M f s))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) ∧
      L.RunGoodL M f s := by
  haveI := L.crunOk_std hL
  rw [← L.mach_std]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  obtain ⟨hA, hG⟩ := backend_correct_program_core_initEXRU L.std (hL.withCrun _) hκ hBR hRC hdet
    hdt hdtr (fun hN => ⟨(hK hN).err, (hK hN).tlsErr, (hK hN).prog, (hK hN).tlsProg⟩) hf M hent
    hres hF hgfree himg hbe hargs hcs hsav hrel hpl hm
  exact ⟨hA, LinkSys.runGoodL_withCrun hG⟩

/-- **`backend_correct_program_initEX` with `DetPRBR`** (`backend_correct_program_initEXRU`,
`DetPRBR.toU`). -/
theorem backend_correct_program_initEXR (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : ∀ M, L.std.DetPRBR κ M) (hdt : ∀ M, L.std.DetTabPRBE κ M)
    (hdtr : ∀ M, L.std.DetTabPRBr κ M) (hK : L.HooksKeep)
    {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) (L.std.iniOf M f s))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) ∧
      L.RunGoodL M f s :=
  backend_correct_program_initEXRU L hL hκ (fun _ => hBR) (fun _ => hRC)
    (fun _ M => LinkSys.DetPRBR.toU L.std (hdet M)) (fun _ => hdt) (fun _ => hdtr) (fun _ => hK)
    hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun

end E2E

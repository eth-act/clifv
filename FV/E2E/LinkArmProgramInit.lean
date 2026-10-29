import FV.E2E.LinkArmCountPRBSucc

/-!
# The linked program with the slot-byte oracle at a top-level entry (SEM1 #537, #680 (3), (e))

**`backend_correct_program_core_init`**: `backend_correct_program_core`'s returning case for a
CLIF entry memory placed with the slot-byte oracle `ini` (`PlaceAtB`) whose table is the machine
run's (`TableOf M f s ini`): a returning CLIF run of `f`'s activation (program calls atomic,
`envR`) is realised by the linked machine (`ArmRefines`). From `thmPRBRL_allC` (the scope
conditions `BaseRetOk`, `RetCount`; `DetPRB`, `DetTabPRB` at every depth), with the machine entry's
own prophecies (`prophOf`, `prophStOf`) and the return address outside the code (`RaOk`).

**`backend_correct_program_init`**: the same for the whole-program CLIF run of at most `M + 1`
steps (`LinkSys.std`, `Clif.runLoop_linkN`, as `backend_correct_program_budget`).

`TableOf` stays a premise: it presupposes that the program callees the machine calls before its
return return ([#700](https://github.com/eth-act/clifv/issues/700)).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **A returning activation entered from outside, under the slot-byte oracle** (module doc). -/
theorem backend_correct_program_core_init (L : LinkSys) (hL : L.Ok) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g) (hdet : ∀ M, L.DetPRB κ M)
    (hdt : ∀ M, L.DetTabPRB κ M) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} {ini : Clif.SlotInit}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) ini)
    (htab : L.TableOf M f s ini) {fuel : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop (L.envR M f) L.P.bare fuel cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntryB κ M f L.F args cs w₀ ini := by
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
  obtain ⟨us, outs, wf, n, e, hus, hlen, hhold, hmemR, -, hret, -⟩ :=
    L.thmPRBRL_allC hL hκ hBR hRC hdet hdt M f hf L.F args cs w₀ fuel vals cm ini L.Img ra s hWE
      hMEP hra htab hrun
  exact armRefines_of_actRet hus hlen hhold hmemR hret

/-- **The whole-program run under the slot-byte oracle** (module doc): a returning whole-program
CLIF run of at most `M + 1` steps from `f`'s entry placed with `ini`, the machine's table, is
realised by the linked machine of depth `M`. -/
theorem backend_correct_program_init (L : LinkSys) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hBR : L.BaseRetOk)
    (hRC : ∀ g ∈ L.P.funcs, L.RetCount g)
    (hdet : ∀ M, L.std.DetPRB κ M) (hdt : ∀ M, L.std.DetTabPRB κ M) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} {ini : Clif.SlotInit}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAtB cs.mem (spv w₀) ini)
    (htab : L.std.TableOf M f s ini) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefines (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
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
  exact backend_correct_program_core_init L.std (hL.withCrun _) hκ hBR hRC hdet hdt hf M hent hres
    hF hgfree himg hbe hargs hcs hsav hrel hpl htab hm

end E2E

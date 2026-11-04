import FV.E2E.LinkArmUInd

/-!
# The whole-program theorem with unwinding (S10f, #233)

`backend_correct_program_core`/`_budget` (`FV/E2E/LinkArm.lean`) for the linked machine with
unwinding (`LinkSysU.machU`) and the whole-program CLIF run with unwinding:

* `backend_correct_program_coreU`: from the linking statement with unwinding at depth `M`
  (`LinkSysU.ThmU`), for an outcome `o` of `f`'s activation that, when it returns, traps or
  unwinds, is a run with unwinding of the program without functions under `envRX M f`, the linked
  machine with unwinding of depth `M` refines `o` (`ArmRefinesU`; an exception leaving `f` is an
  AAPCS64 return to the caller with the exception object in x0 and the live memory agreeing).
* `backend_correct_program_budgetU_of`: the whole-program run with unwinding of at most `M + 1`
  steps (`LinkSysU.stdX`), from the linking statement at depth `M`.
* **`backend_correct_program_budgetU`**, **`backend_correct_program_peakU`**: the same without the
  linking statement as a premise, which holds at every depth (`LinkSysU.thmU`) when the linking
  needs no non-interference (`¬ NeedNI`: no program callee has an outgoing-argument area or a slot
  region).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The whole-program theorem with unwinding for any callee runs**, from the linking statement
at depth `M`. -/
theorem backend_correct_program_coreU (L : LinkSysU) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) (hthm : L.ThmU κ M) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.envRX M f) L.P.bare cs) {o : Clif.XOutcome}
    (hlink : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c) ∨
      (∃ e cm, o = .unwound e cm)) → ∃ m, Clif.runLoopX (L.envRX M f) L.P.bare m cs.toX = o) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s o := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
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
      have := L.toLinkSys.frameSize_mod hL hf
      omega
  -- the machine side
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  cases o with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals cm =>
    obtain ⟨m, hm⟩ := hlink (.inl ⟨_, _, rfl⟩)
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall, -⟩ :=
      (hthm f hf L.F args cs w₀ m hWE).1 vals cm hm
    obtain ⟨n, hret, -⟩ := hall L.Img ra s hME
    exact armRefines_of_actRet (fb := (L.A f).fb) (base := (L.A f).base) hus hlen hhold hmemR hret
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (.inr (.inl ⟨_, rfl⟩))
    exact (hthm f hf L.F args cs w₀ m hWE).2.1 htr c hm L.Img ra s hME
  | unwound e cm =>
    obtain ⟨m, hm⟩ := hlink (.inr (.inr ⟨_, _, rfl⟩))
    obtain ⟨obj, wf, hex, hmemR, hall, -⟩ := (hthm f hf L.F args cs w₀ m hWE).2.2 e cm hm
    obtain ⟨n, hu, -⟩ := hall L.Img ra s hME
    exact ⟨n, hu.ret, by rw [hu.x0]; exact hex, memAgree_of hmemR hu.mem⟩

/-- **The whole-program theorem with unwinding for the runs of at most `M + 1` steps**
(`backend_correct_program_budget`'s counterpart), from the linking statement at depth `M` of the
default callee runs (`LinkSysU.stdX`). -/
theorem backend_correct_program_budgetU_of (L : LinkSysU) (hL : L.Ok) (hU : L.OkU)
    {κ : Nat → Clif.Function → Nat} {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) (hthm : L.stdX.ThmU κ M) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  haveI := L.crunOkX_std hL fun g hg hn => hU.indScopeX g hg hn
  rw [show L.machU M f = L.stdX.machU M f from (L.machU_withCrunX _ M f).symm]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_coreU L.stdX hL hf M hthm hent hres hF hgfree himg
    hbe hargs hcs hsav hrel hpl htr fun ho => ?_
  exact L.stdX.envRX_crun hL.names M hf (runInv_entry hf hcs) hIf (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [show L.stdX.crunX (M + 1) cs =
      Clif.runLoopX L.envX L.P (M + 1) cs.toX from rfl, ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [show L.stdX.crunX (M + 1) cs =
      Clif.runLoopX L.envX L.P (M + 1) cs.toX from rfl, ho] <;> exact fun h => nomatch h)

/-- **The whole-program theorem with unwinding for the run's peak call depth**
(`backend_correct_program_peak`'s counterpart): the linked machine of depth `d`, the peak call
depth of the whole-program run with unwinding (`Clif.DepthLeX`), from the linking statement at
depth `d` of the callee runs of fuel `F` (`LinkSysU.peakX`). -/
theorem backend_correct_program_peakU_of (L : LinkSysU) (hL : L.Ok) (hU : L.OkU)
    {κ : Nat → Clif.Function → Nat} {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) (hthm : (L.peakX F).ThmU κ d) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX F).envRX d f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU d f) s
      (Clif.runLoopX L.envX L.P (F + 1) cs.toX) := by
  rw [show L.machU d f = (L.peakX F).machU d f from (L.machU_withCrunX _ d f).symm]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_coreU (L.peakX F) hL hf d hthm hent hres hF hgfree himg
    hbe hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoopX_linkD (env := L.envX) (syms := L.syms) F d hL.names hf hL.free
    (hU.indScopeX f hf) (E := (L.peakX F).envRX d f) rfl rfl
    (fun _ hn => (L.peakX F).envRX_of (.inl hn)) ((L.peakX F).envRX_link hL.names)
    (F + 1) cs.toX (Nat.le_refl _) hd (LinkSysU.xinv_toX (runInv_entry hf hcs)) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

/-- The premises with unwinding do not depend on the callee runs. -/
theorem LinkSysU.OkU.withCrunX {L : LinkSysU} (hU : L.OkU) (c : Nat → Clif.State → Clif.XOutcome) :
    (L.withCrunX c).OkU :=
  ⟨hU.envX, hU.lowerU, hU.sites, hU.rows, hU.pads, hU.last, hU.saved, hU.indScopeX, hU.baseXR,
    hU.baseXRI, hU.baseExcl, hU.baseRaiseExt, hU.baseUnw, hU.baseNoRaise, hU.baseKeepsPlaceU,
    hU.baseKeepsAllocsU⟩

/-- **The whole-program theorem with unwinding for the runs of at most `M + 1` steps**
(`backend_correct_program_budget`'s counterpart, without non-interference): for a function `f` of a
linked program with unwinding whose premises hold (`Ok`, `OkU`), a stack budget `κ` and no program
callee with an outgoing-argument area or a slot region (`¬ NeedNI`), the linked machine with
unwinding of depth `M` refines `f`'s whole-program run with unwinding of at most `M + 1` steps
(`ArmRefinesU`: a return is an ABI return with the results, a trap the trap site, an exception
leaving `f` an ABI return to the caller with the exception object in x0). -/
theorem backend_correct_program_budgetU (L : LinkSysU) (hL : L.Ok) (hU : L.OkU)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hN : ¬ L.NeedNI) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU M f) s
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  haveI := L.crunOkX_std hL fun g hg hn => hU.indScopeX g hg hn
  exact backend_correct_program_budgetU_of L hL hU hf M (L.stdX.thmU hL (hU.withCrunX _) hκ hN M) hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr

/-- **The whole-program theorem with unwinding for the run's peak call depth**
(`backend_correct_program_peak`'s counterpart, without non-interference): the linked machine with
unwinding of depth `d`, the peak call depth of the whole-program run with unwinding
(`Clif.DepthLeX`), refines that run of fuel `F + 1`. -/
theorem backend_correct_program_peakU (L : LinkSysU) (hL : L.Ok) (hU : L.OkU)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (hN : ¬ L.NeedNI) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX F).envRX d f) L.P.bare cs) :
    ArmRefinesU (L.A f).fb (L.A f).base ra (L.machU d f) s
      (Clif.runLoopX L.envX L.P (F + 1) cs.toX) := by
  haveI := L.crunOkX_peak hL (fun g hg hn => hU.indScopeX g hg hn) F
  exact backend_correct_program_peakU_of L hL hU hf F d ((L.peakX F).thmU hL (hU.withCrunX _) hκ hN d) hent
    hres hF hgfree himg hbe hargs hcs hsav hrel hpl hd htr

end E2E

import FV.E2E.LinkArmUProg
import FV.E2E.LinkArmUIndGood

/-!
# The whole-program theorem with unwinding, with the per-state facts of the run (S10g, #404)

`backend_correct_program_coreX`/`_budgetX`/`_peakX` (`FV/E2E/LinkGood.lean`) for the linked
machine with unwinding: for a returning, trapping or unwinding whole-program run with unwinding,
every state of the run of the entered function on `machU` whose step ends without error, and of
every activation nested through its calls (returning or raising), has the per-state facts
(`RunGoodLU`, from the linking statement with the per-state facts `ThmGU`).

* `runGoodLU_withCrunX`: `RunGoodLU` does not depend on the callee runs (the machine does not
  read them).
* `backend_correct_program_coreUG`: from the linking statement at depth `M`;
  `backend_correct_program_budgetUG'`/`_peakUG'`: the premises of
  `backend_correct_program_budgetU'`/`_peakU'`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)

theorem hooksU_withCrunX (c : Nat → Clif.State → Clif.XOutcome) (M : Nat) :
    (L.withCrunX c).hooksU M = L.hooksU M := by
  simp only [hooksU, layer_withCrunX]

theorem UU_withCrunX (c : Nat → Clif.State → Clif.XOutcome) (M : Nat) :
    (L.withCrunX c).UU M = L.UU M := by
  simp only [UU, layer_withCrunX]

theorem reachLU_withCrunX {c : Nat → Clif.State → Clif.XOutcome} {M : Nat} {f : Clif.Function}
    {c0 : Arm.ArmState} {M' : Nat} {g : Clif.Function} {c' t : Arm.ArmState}
    (h : L.ReachLU M f c0 M' g c' t) : (L.withCrunX c).ReachLU M f c0 M' g c' t := by
  induction h with
  | act hj =>
    rw [← L.machU_withCrunX c] at hj ⊢
    exact .act hj
  | nest hj hc herr _ ih =>
    rw [← L.machU_withCrunX c] at hj hc herr ih
    exact .nest hj hc herr ih

theorem goodAtU_withCrunX {c : Nat → Clif.State → Clif.XOutcome} {M : Nat} {g : Clif.Function}
    {c0 t : Arm.ArmState} (h : (L.withCrunX c).GoodAtU M g c0 t) : L.GoodAtU M g c0 t := by
  obtain ⟨X, XR, K, G, gv, heq, hg, hi⟩ := h
  rw [L.hooksU_withCrunX, L.UU_withCrunX, L.machU_withCrunX] at heq
  rw [L.hooksU_withCrunX, L.UU_withCrunX] at hg
  exact ⟨X, XR, K, G, gv, heq, hg, hi⟩

/-- **`RunGoodLU` does not depend on the callee runs** of the linked system with unwinding (the
machine does not read them). -/
theorem runGoodLU_withCrunX {c : Nat → Clif.State → Clif.XOutcome} {M : Nat} {f : Clif.Function}
    {s : Arm.ArmState} (h : (L.withCrunX c).RunGoodLU M f s) : L.RunGoodLU M f s :=
  fun M' g c' t hR he => L.goodAtU_withCrunX
    (h M' g c' t (L.reachLU_withCrunX hR) (by rw [L.machU_withCrunX]; exact he))

end LinkSysU

/-- **The per-state facts of the whole-program run with unwinding** for any callee runs, from the
linking statement at depth `M` (`backend_correct_program_coreU`'s per-state part): for a
returning, trapping or unwinding outcome, `RunGoodLU` of the entered activation. -/
theorem backend_correct_program_coreUG (L : LinkSysU) (hL : L.Ok)
    {κ : Nat → Clif.Function → Nat} {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) (hthm : L.ThmGU κ M) {ra : BitVec 64} {s w₀ : Arm.ArmState}
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
      (∃ e cm, o = .unwound e cm)) → ∃ m, Clif.runLoopX (L.envRX M f) L.P.bare m cs.toX = o)
    (hout : (∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c) ∨
      (∃ e cm, o = .unwound e cm)) :
    L.RunGoodLU M f s := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
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
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  obtain ⟨m, hm⟩ := hlink hout
  rcases hout with ⟨vals, cm, rfl⟩ | ⟨c, rfl⟩ | ⟨e, cm, rfl⟩
  · obtain ⟨us, outs, wf, -, -, -, -, -, hall, -⟩ := (hthm f hf L.F args cs w₀ m hWE).1 vals cm hm
    obtain ⟨n, -, -, -, hrg⟩ := hall L.Img ra s hME
    exact hrg
  · obtain ⟨n, -, hrg⟩ := (hthm f hf L.F args cs w₀ m hWE).2.1 htr c hm L.Img ra s hME
    exact hrg
  · obtain ⟨obj, wf, -, -, hall, -⟩ := (hthm f hf L.F args cs w₀ m hWE).2.2 e cm hm
    obtain ⟨n, -, -, -, -, hrg⟩ := hall L.Img ra s hME
    exact hrg

/-- **`backend_correct_program_budgetU'` with the run's per-state facts**: for a returning,
trapping or unwinding whole-program run with unwinding of at most `M + 1` steps, `RunGoodLU` of
the entered activation on the linked machine with unwinding of depth `M`. -/
theorem backend_correct_program_budgetUG' (L : LinkSysU) (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
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
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs)
    (hout : (∃ vals cm, Clif.runLoopX L.envX L.P (M + 1) cs.toX = .returned vals cm) ∨
      (∃ c, Clif.runLoopX L.envX L.P (M + 1) cs.toX = .trapped c) ∨
      (∃ e cm, Clif.runLoopX L.envX L.P (M + 1) cs.toX = .unwound e cm)) :
    L.RunGoodLU M f s := by
  haveI := L.crunOkX_std hL fun g hg hn => hU.indScopeX g hg hn
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine L.runGoodLU_withCrunX (backend_correct_program_coreUG L.stdX hL hf M
    (L.stdX.thmUNG hL (hU.withCrunX _) ⟨hNI.baseRaiseNI⟩ hκ M) hent hres hF hgfree himg hbe hargs
    hcs hsav hrel hpl htr (fun ho => ?_) hout)
  exact L.stdX.envRX_crun hL.names M hf (runInv_entry hf hcs) hIf (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [show L.stdX.crunX (M + 1) cs =
      Clif.runLoopX L.envX L.P (M + 1) cs.toX from rfl, ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [show L.stdX.crunX (M + 1) cs =
      Clif.runLoopX L.envX L.P (M + 1) cs.toX from rfl, ho] <;> exact fun h => nomatch h)

/-- **`backend_correct_program_peakU'` with the run's per-state facts**: for a returning,
trapping or unwinding whole-program run with unwinding of fuel `F + 1` of peak call depth `d`,
`RunGoodLU` of the entered activation on the linked machine with unwinding of depth `d`. -/
theorem backend_correct_program_peakUG' (L : LinkSysU) (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
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
    (htr : TrapsExplicitX ((L.peakX F).envRX d f) L.P.bare cs)
    (hout : (∃ vals cm, Clif.runLoopX L.envX L.P (F + 1) cs.toX = .returned vals cm) ∨
      (∃ c, Clif.runLoopX L.envX L.P (F + 1) cs.toX = .trapped c) ∨
      (∃ e cm, Clif.runLoopX L.envX L.P (F + 1) cs.toX = .unwound e cm)) :
    L.RunGoodLU d f s := by
  haveI := L.crunOkX_peak hL (fun g hg hn => hU.indScopeX g hg hn) F
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine L.runGoodLU_withCrunX (backend_correct_program_coreUG (L.peakX F) hL hf d
    ((L.peakX F).thmUNG hL (hU.withCrunX _) ⟨hNI.baseRaiseNI⟩ hκ d) hent hres hF hgfree himg hbe
    hargs hcs hsav hrel hpl htr (fun ho => ?_) hout)
  exact Clif.runLoopX_linkD (env := L.envX) (syms := L.syms) F d hL.names hf hL.free
    (hU.indScopeX f hf) (E := (L.peakX F).envRX d f) rfl rfl
    (fun _ hn => (L.peakX F).envRX_of (.inl hn)) ((L.peakX F).envRX_link hL.names)
    (F + 1) cs.toX (Nat.le_refl _) hd (LinkSysU.xinv_toX (runInv_entry hf hcs)) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ | ⟨_, _, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

end E2E

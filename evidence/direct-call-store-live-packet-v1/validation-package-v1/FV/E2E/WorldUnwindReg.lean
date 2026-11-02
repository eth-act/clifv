import FV.E2E.WorldUnwindCore
import FV.E2E.LinkWorld
import FV.E2E.UnwindValueSem

/-!
# The register-level world theorem with unwinding (S10f, #233)

`regLevelCorrect_world` (`FV/E2E/RegLevelCorrect.lean`, the world form `FV/E2E/LinkWorld.lean`
composes) for the machine with unwinding, generic in the activation semantics, from the
trace-keeping core `regLevelCorrect_coreUT`:

* `regLevelCorrect_worldUT`: for a `checkAlloc`-accepted allocation and every initial vreg file,
  every return of the prepared VCode is an `ActRet` with `PostTrace`, every trap a `TrapAt`, and
  every exceptional end an `ActUnw` with `PostTrace` whose last step leaves the frame by unwinding
  (`UnwExit`); the tables the unwinder reads are the emitted ones (`callSites`, `unwindRows`).
* `realizes_valueU_world`: the realisation of the value semantics with unwinding at every
  activation with kept addresses `G` and GOT pins `gv` (`realizes_value_allU`,
  `realizesTryRaise_of_tables`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.UnwindTables Backend.DeadCleanup

/-- `PostTrace` from the trace predicate of the runs with unwinding. -/
theorem postTrace_of_goodXU {R : RLU} {n : Nat}
    (h : ∀ i < n, R.GoodXU (runX R.stepU i R.s0)) :
    PostTrace R.fa R.af R.base R.stepU R.s0 n := by
  intro i _ hi hpc
  rcases h i hi with g | g
  · exact g.good.resolve_left fun h => h hpc
  · exact g.good.resolve_left fun h => h hpc

/-- **The register-level world theorem with unwinding**, generic in the activation semantics
`semU` (realised by the machine with unwinding, `hRz`; `csem` at the returns and traps). -/
theorem regLevelCorrect_worldUT {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {base ra : BitVec 64} {s : Arm.ArmState}
    (hent : AbiCall fb base ra s) (hres : StackAvail K af s)
    (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a) {semU : Sem}
    (hgot : GotSem gv X semU)
    (hRz : ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w =
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w, VReturns vcp semU ρ₀ w₀ us vals w →
      ∃ n, ActRet ra (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af G s) G us vals w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
        PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
        ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) ∧
    (∀ c, VTraps vcp semU ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (runX (Unw.ArmStepU X H U T fa) n s)) ∧
    (∀ obj w, VUnwinds vcp semU XR ρ₀ w₀ obj w →
      ∃ n, ActUnw ra (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af G s) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
        PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
        UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  have hR : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ : RLU).Wf :=
    ⟨⟨cc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩,
      hent.program, hG⟩
  obtain ⟨_, h1, h2, h3⟩ := regLevelCorrect_coreUT hR hent hat hU hgot (hRz lm psF _ rfl hR) hrets
    hhalt (lsda_cases hsites hlsda) (siteAt_of_check hR hlast) hrows hcie hfde hsaved hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  refine ⟨fun us vals w hret => ?_, h2, fun obj w hu => ?_⟩
  · obtain ⟨n, a1, a2, a3, a4, a5, a6, htr, hnot⟩ := h1 us vals w hret
    exact ⟨n, ⟨a1, a2, a3, a4, a5, a6⟩, postTrace_of_goodXU htr, hnot⟩
  · obtain ⟨n, a1, a2, a3, a4, a5, a6, htr, hn, hx⟩ := h3 obj w hu
    exact ⟨n, ⟨a1, a2, a3, a4, a5, a6⟩, postTrace_of_goodXU htr, hn, hx⟩

/-- **The register-level world theorem with unwinding, with the per-state facts of the run**
(`regLevelCorrect_worldUT` for a semantics realised with the trace `RLU.GoodXUF`): every state
before a return, a trap or an exceptional end has `actGoodXU`, and after a trap every state
errs. -/
theorem regLevelCorrect_worldUTG {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat} {G : BitVec 64 → Prop}
    {gv : Nat → String → Prop} {base ra : BitVec 64} {s : Arm.ArmState}
    (hent : AbiCall fb base ra s) (hres : StackAvail K af s)
    (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a) {semU : Sem}
    (hgot : GotSem gv X semU)
    (hRz : ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) R.GoodXUF)
    (hrets : ∀ us uses w, semU (.rets us) uses w =
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
        ⟨fa.k, af.slotBase⟩ X i uses w = some (outs, w', .halt))
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hlast : lastCallsOk af fa = true) {rows : List (Nat × Cfi)}
    (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) {w₀ : Arm.ArmState}
    (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) vcp.EntryArg af s w₀) (ρ₀ : Nat → CV) :
    (∀ us vals w, VReturns vcp semU ρ₀ w₀ us vals w →
      ∃ n, ActRet ra (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af G s) G us vals w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
        PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧
        ¬ UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
        ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G gv
          (runX (Unw.ArmStepU X H U T fa) i s)) ∧
    (∀ c, VTraps vcp semU ρ₀ w₀ c →
      ∃ n, TrapAt fb base c (runX (Unw.ArmStepU X H U T fa) n s) ∧
        (∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G gv
          (runX (Unw.ArmStepU X H U T fa) i s)) ∧
        ∀ m, Arm.r .ERR (runX (Unw.ArmStepU X H U T fa) (n + m + 1) s) ≠ .None) ∧
    (∀ obj w, VUnwinds vcp semU XR ρ₀ w₀ obj w →
      ∃ n, ActUnw ra (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
          af G s) G obj w s (runX (Unw.ArmStepU X H U T fa) n s) ∧
        PostTrace fa af base (Unw.ArmStepU X H U T fa) s n ∧ 0 < n ∧
        UnwExit U T fa (runX (Unw.ArmStepU X H U T fa) (n - 1) s) ∧
        ∀ i < n, actGoodXU vcp rf af fa fb base s X H XR U T K G gv
          (runX (Unw.ArmStepU X H U T fa) i s)) := by
  obtain ⟨cc, ins, hc⟩ := checked_of_checkAlloc hcheck
  obtain ⟨a0, hat, hle⟩ := hc.at
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  have hR : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ : RLU).Wf :=
    ⟨⟨cc, ins, a0, hat, entryOk_of_le hle⟩, halloc, hemit, hlayout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩,
      hent.program, hG⟩
  obtain ⟨_, h1, h2, h3⟩ := regLevelCorrect_coreUTP hR hent hat hU hgot (fun _ h => .inl h)
    (fun _ h => .inr h) (hRz lm psF _ rfl hR) hrets
    hhalt (lsda_cases hsites hlsda) (siteAt_of_check hR hlast) hrows hcie hfde hsaved hbe
    (fun _ => ρ₀) (fun _ => Inv_mono hle Inv_entryState)
  refine ⟨fun us vals w hret => ?_, fun c htc => ?_, fun obj w hu => ?_⟩
  · obtain ⟨n, a1, a2, a3, a4, a5, a6, htr, hnot⟩ := h1 us vals w hret
    exact ⟨n, ⟨a1, a2, a3, a4, a5, a6⟩, postTrace_of_goodXU fun i hi => (htr i hi).goodXU, hnot,
      fun i hi => actGoodXU_of hR hU hrows hcie hfde hsaved (htr i hi)⟩
  · obtain ⟨n, htrap, htr, hst⟩ := h2 c htc
    exact ⟨n, htrap, fun i hi => actGoodXU_of hR hU hrows hcie hfde hsaved (htr i hi), hst⟩
  · obtain ⟨n, a1, a2, a3, a4, a5, a6, htr, hn, hx⟩ := h3 obj w hu
    exact ⟨n, ⟨a1, a2, a3, a4, a5, a6⟩, postTrace_of_goodXU fun i hi => (htr i hi).goodXU, hn, hx,
      fun i hi => actGoodXU_of hR hU hrows hcie hfde hsaved (htr i hi)⟩

/-- **The realisation of the value semantics with unwinding at an activation with kept addresses
`G` and GOT pins `gv`**: from the callee contracts relative to `G` (`CalleeOkG`,
`CalleeTryOkG`), `TlsOk`, the form coverage, the raising callees' contract and the emitted
call-site table. -/
theorem realizes_valueU_world {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {base : BitVec 64} {s : Arm.ArmState}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K G s (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K X H)
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (valueSemVU gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (QA R.toRL) R.GoodXU := by
  intro lm psF R hReq hR
  subst hReq
  exact realizes_value_allU hR hC hCT hTls hcov hU
    (realizesTryRaise_of_tables hR hU (tryRaiseSem_valueSemVU _ _ _ _ _)
      (gotSem_valueSemVU _ _ _ _ _) hsites hlsda
      (padsNonzero_of_check hpad) hlast)

/-- **The realisation of `csemU` with GOT pins `gv` (`csemVU gv`) at an activation with kept
addresses `G`** (`realizes_all` transferred by `realizes_allU`, `realizesTryRaise_of_tables`). -/
theorem realizes_csemU_world {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {base : BitVec 64} {s : Arm.ArmState}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K G s (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K X H)
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (csemVU gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (QA R.toRL) R.GoodXU := by
  intro lm psF R hReq hR
  subst hReq
  exact realizes_allU hR hU (realizes_all hR hC hCT hTls hcov) (fun _ _ _ h => csemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [csemVU_call_raise h hr])
    (realizesTryRaise_of_tables hR hU (tryRaiseSem_csemVU _ _ _ _ _) (gotSem_csemVU _ _ _ _ _)
      hsites hlsda
      (padsNonzero_of_check hpad) hlast)

/-- **`realizes_valueU_world` with the raising-call states' step facts** (trace `R.GoodXUF`). -/
theorem realizes_valueU_worldF {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {base : BitVec 64} {s : Arm.ArmState}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K G s (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K X H)
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (valueSemVU gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (QA R.toRL) R.GoodXUF := by
  intro lm psF R hReq hR
  subst hReq
  exact realizes_value_allUF hR hC hCT hTls hcov hU
    (realizesTryRaise_of_tablesF hR hU (tryRaiseSem_valueSemVU _ _ _ _ _)
      (gotSem_valueSemVU _ _ _ _ _) hsites hlsda
      (padsNonzero_of_check hpad) hlast)

/-- **`realizes_csemU_world` with the raising-call states' step facts** (trace `R.GoodXUF`). -/
theorem realizes_csemU_worldF {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    {G : BitVec 64 → Prop} {gv : Nat → String → Prop} {base : BitVec 64} {s : Arm.ArmState}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : CalleeOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) X H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → CalleeTryOkG (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K G s (CallAt fa base) X H vcp.TrySite gv)
    (hTls : vcp.hasTls = true → TlsOk (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) K X H)
    (hU : CalleeUnwOkG (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size
      af G s) K G s (CallAt fa base) X XR U vcp.CallSite gv)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, G, gv⟩, XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf (csemVU gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (QA R.toRL) R.GoodXUF := by
  intro lm psF R hReq hR
  subst hReq
  exact realizes_allUP hR (fun _ h => .inl h) hU (realizes_all hR hC hCT hTls hcov)
    (fun _ _ _ h => csemVU_noRaise h)
    (fun _ _ _ _ _ _ h hr => by rw [csemVU_call_raise h hr])
    (realizesTryRaise_of_tablesF hR hU (tryRaiseSem_csemVU _ _ _ _ _) (gotSem_csemVU _ _ _ _ _)
      hsites hlsda
      (padsNonzero_of_check hpad) hlast)

end E2E

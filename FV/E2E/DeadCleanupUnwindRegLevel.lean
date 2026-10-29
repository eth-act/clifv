module

public import FV.E2E.RegLevelCorrectU
public import FV.E2E.UnwindValueSem

@[expose] public section

/-!
# The register-level layer with unwinding for the dead-cleanup chain (S10e, #232)

`regLevelCorrect_backend_ex_value`'s counterpart (`FV/E2E/DeadCleanupRegLevel.lean`): the
generic register-level theorem with unwinding (`regLevelCorrect_backend_exU_of`,
`FV/E2E/RegLevelCorrectU.lean`) for the value semantics with unwinding `valueSemU`, realised by
`realizes_value_allU` (the old value realiser `realizes_value_all` transferred to the machine
with unwinding) with the raising `tryCall` case of `realizesTryRaise_of_tables`.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables Backend.DeadCleanup

/-- **The realisation of `valueSemU`** for every activation of the compiled function (no kept
addresses, no GOT pinning; `realizes_csemU_backend`'s counterpart). -/
theorem realizes_valueU_backend {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true) :
    ∀ base s lm psF (R : RLU),
      R = ⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
        XR, U, T⟩ → R.Wf →
      Realizes R.vc R.rf
        (valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          ⟨fa.k, af.slotBase⟩ X XR) ckeep R.stepU
        (fun s c => Q R.toRL s c ∧ AInv R.toRL c) R.GoodXU := by
  intro base s lm psF R hReq hR
  subst hReq
  have hF : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
      XR, U, T⟩ : RLU).F =
      frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s :=
    frameWG_false K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s
  have hU' := hU base s
  rw [← hF] at hU'
  have h := realizes_value_allU hR (by rw [hF]; exact (hC s).g _ s _ _)
    (by rw [hF]; exact fun h => (hCT h s).g _ _ s _ _) (by rw [hF]; exact fun h => hTls h s)
    hcov hU'
    (realizesTryRaise_of_tables hR hU' (tryRaiseSem_valueSemVU _ _ _ _ _)
      (gotSem_valueSemVU _ _ _ _ _) hsites hlsda
      (padsNonzero_of_check hpad) hlast)
  have e : (⟨⟨vcp, rf, af, fa, fb, lm, base, s, X, H, psF, K, fun _ => False, fun _ _ => False⟩,
      XR, U, T⟩ : RLU).valueSemU =
      valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XR := by
    rw [RLU.valueSemU, hF]
    exact valueSemVU_bot _ _ _ _
  rw [e] at h
  exact h

/-- `valueSemU` is `csem` at the returns. -/
theorem valueSemU_rets {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    (us : List (Reg × Reg)) (uses : List CV) (w : Arm.ArmState) :
    valueSemU F ctx X XR (.rets us) uses w = csem F ctx X (.rets us) uses w := by
  rw [← valueSemVU_bot, valueSemVU_rets]

/-- A trap instruction's `.halt` under `valueSemU` is one of `csem`. -/
theorem valueSemU_halt_trap {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {XR : XRaise}
    {i : MInst} {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (ht : trapCode? i ≠ none) (h : valueSemU F ctx X XR i uses w = some (outs, w', .halt)) :
    csem F ctx X i uses w = some (outs, w', .halt) := by
  rw [← valueSemVU_bot] at h
  exact valueSemVU_halt_trap ht h

/-- **`RegLevelCorrect` with unwinding for the backend's code under the value semantics**
(`RegLevelCorrectUEx`, an `AllocChecked` allocation; `regLevelCorrect_backend_ex_value`'s
counterpart): the premises of `regLevelCorrect_backend_exU`. -/
theorem regLevelCorrect_backend_exU_value {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : AllocChecked vcp rf) (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectUEx
      (fun s => valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XR)
      XR (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb :=
  regLevelCorrect_backend_exU_of hcheck halloc hemit hlayout
    (realizes_valueU_backend hcov hC hCT hTls hU hsites hlsda hpad hlast) (fun _ => valueSemU_rets)
    (fun _ _ _ _ _ _ ht h => valueSemU_halt_trap ht h) hU (lsda_cases hsites hlsda) hlast
    hrows hcie hfde hsaved

/-- **`RegLevelCorrectU` for the backend's code under the value semantics** (a
`checkAlloc`-accepted allocation, every initial vreg file). -/
theorem regLevelCorrect_backendU_value {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} (hcheck : checkAlloc vcp rf = .ok ())
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {X : ExtSem} {H : ArmHooks}
    {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : vcp.hasTryCall = true → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : vcp.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true) :
    RegLevelCorrectU
      (fun s => valueSemU (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XR)
      XR (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af) K
      (Unw.ArmStepU X H U T fa) vcp af fb :=
  regLevelCorrect_backendU_of hcheck halloc hemit hlayout
    (realizes_valueU_backend hcov hC hCT hTls hU hsites hlsda hpad hlast) (fun _ => valueSemU_rets)
    (fun _ _ _ _ _ _ ht h => valueSemU_halt_trap ht h) hU (lsda_cases hsites hlsda) hlast
    hrows hcie hfde hsaved

/-! ## Non-vacuity -/

namespace DeadCleanupUnwindRegLevelWitness

open RegLevelCorrectUWitness

/-- `regLevelCorrect_backendU_value` applies to the witness function of
`FV/E2E/RegLevelCorrectU.lean` (a compiled function with a call) with `regLevelCorrect_backend`'s
premises only (its unwinding premises are `RegLevelCorrectUWitness.premises`). -/
theorem backendU_value_applies {X : ExtSem} {H : ArmHooks} {K : Nat} {fb : FnBin}
    (hlayout : fa.layout = .ok fb) (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vc)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H vc.CallSite)
    (hTls : vc.hasTls = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s) K X H) :
    RegLevelCorrectU
      (fun s => valueSemU (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af s)
        ⟨fa.k, af.slotBase⟩ X XRaise.none)
      XRaise.none (frameW K (RAFrame.compute vc rf).intBase (RAFrame.compute vc rf).size af) K
      (Unw.ArmStepU X H Unw.UnwHooks.none T fa) vc af fb := by
  obtain ⟨hca, halloc, hemit, -, -, -, hU, hsites, hlsda, hpad, hlast, hrows, hcie, hfde,
    hsaved⟩ := premises K X
  have hnt : vc.hasTryCall = false := by decide +kernel
  exact regLevelCorrect_backendU_value hca halloc hemit hlayout hcov hC
    (fun h => absurd h (by rw [hnt]; decide)) hTls hU hsites hlsda hpad hlast hrows hcie hfde
    hsaved

end DeadCleanupUnwindRegLevelWitness

end Backend.Proof

import FV.E2E.Final
import FV.E2E.IselSimU
import FV.E2E.UnwindPrepare
import FV.E2E.RegLevelCorrectU
import FV.Backend.Proof.LowerSimUCheck

/-!
# The backend's end-to-end theorem with unwinding (S10e, #232)

`backend_correct_final`'s counterpart for the CLIF runs with unwinding (`Clif.runLoopX`) and
the machine with unwinding `Unw.ArmStepU X H U T fa`: `ArmRefinesU`, whose `unwound e cm` case
is an Arm return to the caller (`ArmRet`) with the exception object in x0 (`ExnRel`) and the
memory agreeing. The layers (`backend_correct_of_layersU_ex`): CLIF → VCode `iselSimU_of_driver`
(the driver's M4 obligations from M4's rule theorems, as in `backend_correct_ex`), `prepare`
`prepareCorrectU_of_check`, VCode → Arm `regLevelCorrect_backend_exU`, all for `csemU`.

* `iselSimU_final`: `IselSimU` for `csemU` from the validators (`lowerCheck`, `unwCheck`) and the
  externs' contracts (`XCallsOk`, `XCallsIndOk`, their exceptional results `XRaiseOk`,
  `XRaiseIndOk`, the exclusivity `XRaiseExcl`).
* `backend_correct_final_unwind_ex` (`CompiledA`), `backend_correct_final_unwind` (`Compiled`).
* `backend_correct_final_of_unwind`: the normal-return theorem's shape (`ArmRefines` of
  `Clif.runLoop` with the machine `ArmStepX`) as the specialisation without raising callees
  (`XRaise.none`, `Unw.UnwHooks.none`; `armRefines_of_armRefinesU`, `Unw.armStepU_none`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables

/-- **CLIF → VCode with unwinding for the backend's code under `csemU`**: the driver's
obligations from M4's rule theorems (as `backend_correct_ex`), the exceptional edges from the
validator `unwCheck`, the callee contracts from the externs' contracts. -/
theorem iselSimU_final {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {fctx : FnCtx}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : XRaiseExcl env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : fctx.slotBase = slotOff) :
    IselSimU (csemU F fctx X XR) XR ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ env p f
      vc := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUS⟩ :=
    loweringU_of_check (show lowerCheckU f vc = true by
      simp [lowerCheckU, hc.lowerOk, hunw])
  have houtB := outgoing_le_intBaseA hc
  have hRef := refines_csemU F fctx X XR
  have hmem : MemRefines F slotOff syms (csemU F fctx X XR) := memRefines_csemU F fctx X XR hslot hsym
  have hcalls := callsRefine_csemU (ctx := fctx) (F := F) hX hXE
  have hicalls := indCallsRefine_csemU (ctx := fctx) (F := F) hXI hXE hsym
    (fun _ _ _ h => h.1.symbols)
  have mrs := mrStable_holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f
  refine iselSimU_of_driver (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A)
    ?_ hUS (driverSem_csemU F fctx X XR) hRef hmem (raiseSem_csemU F fctx X XR)
    (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
    (tryStack_mono (tryStack_of_check hc.lowerOk) houtB)
    (indStack_mono (indStack_of_check hc.lowerOk) houtB) hXR hXRi hsym
  exact {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csemU F fctx X XR).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef mrs hcalls hicalls hmem
      (outArgsOk_holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f)
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef mrs
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨(RAFrame.compute vcp rf).intBase,
      tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef mrs hmem
        (outArgsOk_holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f) hcalls,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef mrs hmem
      (outArgsOk_holds ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }

/-- **The backend's end-to-end theorem with unwinding for an `AllocChecked` allocation**
(`backend_correct_final_ex`'s counterpart): the Arm run of the compiled function on the machine
with unwinding refines the CLIF run with unwinding — returns and traps as before, and a run that
ends by an exception (`unwound e cm`) is an Arm return to the caller with the exception object in
x0 (`ExnRel`) and the memory agreeing. Premises beyond `backend_correct_final_ex`'s: the
exceptional-edge validator `unwCheck`; the externs' exceptional results (`XRaiseOk`,
`XRaiseIndOk`) and their exclusivity with normal returns (`XRaiseExcl`); the raising callees'
contract `CalleeUnwOkG`; the tables the unwinder reads (the emitted call-site table `callSites`,
the CIE and the FDE rows `unwindRows`); the checks `padsNonzeroB`, `lastCallsOk`,
`savedCheck`; `TrapsExplicitX` for the runs with unwinding. -/
theorem backend_correct_final_unwind_ex {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU_ex
    (sem := fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X XR)
    (fun s' => iselSimU_final hsub hc hunw (hX s') (hXI s') (hXR s') (hXRi s') (hXE s') hsym hslot)
    (fun _ => prepareCorrectU_of_check (driverSem_csemU _ _ _ _) hc.prepOk XR)
    (regLevelCorrect_backend_exU hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallA hc h)) (fun h => hTls (hasTls_of_vcodeA hc h)) hUnw
      hsites hlsda hpad hlast hrows hcie hfde hsaved)
    hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs
      (stackArgsAvoid_frameWA hc hres hent hargs))
    hcs hrel htr fuel

/-- **The backend's end-to-end theorem with unwinding** (`Compiled`; `backend_correct_final`'s
counterpart, through `regLevelCorrect_backendU`). -/
theorem backend_correct_final_unwind {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hUnw : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU
    (sem := fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X XR)
    (fun s' => iselSimU_final hsub hc.toA hunw (hX s') (hXI s') (hXR s') (hXRi s') (hXE s') hsym
      hslot)
    (fun _ => prepareCorrectU_of_check (driverSem_csemU _ _ _ _) hc.prepOk XR)
    (regLevelCorrect_backendU hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCall hc h)) (fun h => hTls (hasTls_of_vcode hc h)) hUnw
      hsites hlsda hpad hlast hrows hcie hfde hsaved)
    hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs
      (stackArgsAvoid_frameW hc hres hent hargs))
    hcs hrel htr fuel

/-- **The normal-return theorem's shape as the specialisation without raising callees**: with
`XRaise.none` and `Unw.UnwHooks.none` the machine with unwinding is `ArmStepX`
(`Unw.armStepU_none`), and `ArmRefinesU` of `Clif.runLoopX` gives `ArmRefines` of
`Clif.runLoop` under `env.toEnv` (`armRefines_of_armRefinesU`). -/
theorem backend_correct_final_of_unwind {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    {X : ExtSem} {H : ArmHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XRaise.none)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XRaise.none)
    (hXE : ∀ s, XRaiseExcl env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XRaise.none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    (hpad : padsNonzeroB af fa = true) (hlast : lastCallsOk af fa = true)
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows) (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env.toEnv p fuel cs) := by
  have h := backend_correct_final_unwind (U := Unw.UnwHooks.none) hsub hc hunw hcov hC hCT hTls
    hX hXI hXR hXRi hXE hsym hslot
    (fun _ _ => calleeUnwOkG_none _ _ _ _ _ _ _ _) hsites hlsda hpad hlast hrows hcie hfde hsaved
    hent hres hbe hargs hcs hrel htr fuel
  rw [Unw.armStepU_none] at h
  exact armRefines_of_armRefinesU h

/-! ## Non-vacuity -/

/-- **Non-vacuity of the new premise groups of `backend_correct_final_unwind{,_ex}` and
`backend_correct_final_of_unwind`**: the externs' exceptional contracts hold for externs that
do raise (`IselSimUWitness`: every extern unwinds with a Rust panic, every callee raises object
77), and the per-function unwinding premises (allocation, raising callees' contract, call-site
table, frame rows, checks) hold on a compiled function with a call
(`RegLevelCorrectUWitness.premises`). -/
theorem backend_correct_final_unwind_premises (K : Nat) (X : ExtSem) (exts : List Clif.ExtFunc)
    (sigs : List Clif.Signature) (MR : MemRelT) :
    (XRaiseOk IselSimUWitness.env exts MR X IselSimUWitness.XR ∧
      XRaiseIndOk IselSimUWitness.env sigs MR X IselSimUWitness.XR ∧
      XRaiseExcl IselSimUWitness.env exts sigs MR X IselSimUWitness.XR ∧
      ExnRel (IselSimUWitness.exn 77) 77) ∧
    (∀ base s, CalleeUnwOkG (frameW K (RAFrame.compute RegLevelCorrectUWitness.vc
        RegLevelCorrectUWitness.rf).intBase (RAFrame.compute RegLevelCorrectUWitness.vc
        RegLevelCorrectUWitness.rf).size RegLevelCorrectUWitness.af s) K (fun _ => False) s
      (CallAt RegLevelCorrectUWitness.fa base) X XRaise.none Unw.UnwHooks.none
      RegLevelCorrectUWitness.vc.CallSite (fun _ _ => False)) ∧
    callSites RegLevelCorrectUWitness.af RegLevelCorrectUWitness.fa = .ok none ∧
    padsNonzeroB RegLevelCorrectUWitness.af RegLevelCorrectUWitness.fa = true ∧
    lastCallsOk RegLevelCorrectUWitness.af RegLevelCorrectUWitness.fa = true ∧
    unwindRows RegLevelCorrectUWitness.af RegLevelCorrectUWitness.fa =
      .ok RegLevelCorrectUWitness.rows ∧
    savedCheck RegLevelCorrectUWitness.vc RegLevelCorrectUWitness.rf = true := by
  obtain ⟨-, -, -, -, -, -, hU, hcs, -, hpad, hlast, hrows, -, -, hsaved⟩ :=
    RegLevelCorrectUWitness.premises K X
  exact ⟨⟨IselSimUWitness.xRaiseOk exts MR X, IselSimUWitness.xRaiseIndOk sigs MR X,
    IselSimUWitness.xRaiseExcl exts sigs MR X, IselSimUWitness.exnRel⟩, hU, hcs, hpad, hlast,
    hrows, hsaved⟩

end E2E

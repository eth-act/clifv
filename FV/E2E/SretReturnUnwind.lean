import FV.E2E.IselSimU
import FV.E2E.UnwindPrepare
import FV.E2E.RegLevelCorrectU
import FV.E2E.SretReturn
import FV.Backend.Proof.SretStableX
import FV.Backend.Proof.LowerSimUAbi

/-!
# The `sret` return register with unwinding (S7)

`SretReturn.lean`'s ABI return values for the backend's theorem with unwinding
(`backend_correct_final_unwind`): a return also leaves `sretArg f args`, the `sret` argument, in
x0 after the CLIF return values.

* `IselSimUAbi`, `iselSimUAbi_of_driver`, `iselSimU_final_abi`: the CLIF → VCode layer with
  unwinding with all ABI returns held (`driver_correctU_abi` with `sret_reachX`: the `sretRet f`
  value at every `return` is the `sret` argument, for functions with `sretStableXB f` — the
  `sret` value is bound once, also on the exceptional edges to the handler blocks);
* `ArmRefinesUAbi`: `ArmRefinesU` with `vals ++ rets` in x0.. (`ArmRefinesUAbi.armRefinesU`);
* `backend_correct_of_layersU_ex_abi`, `backend_correct_final_unwind_ex_abi`,
  **`backend_correct_final_unwind_abi`**: `backend_correct_final_unwind[_ex]` with the premise
  `sretStableXB f = true`;
* **`backend_correct_final_unwind_sret`**: for a function with an `sret` parameter `i` and no
  returns, a return of the run with unwinding leaves the `sret` argument `args[i]` in x0.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.UnwindTables

/-- **CLIF → VCode with unwinding, with the ABI return values**: `IselSimU`, and the returned
use values hold the CLIF return values followed by `sretArg f args` (`AllHold`). -/
def IselSimUAbi (sem : Sem) (XR : XRaise) (Γ : Rel) (env : Clif.XEnv) (p : Clif.Program)
    (f : Clif.Function) (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsAtEntry Γ.F f.sig args w₀ → TrapsExplicitX env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        AllHold (vals ++ sretArg f args) outs ∧ MemRel Γ.F Γ.syms cm w) ∧
    (∀ c, Clif.runLoopX env p fuel cs.toX = .trapped c → VTraps vc sem ρ₀ w₀ c) ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w, VUnwinds vc sem XR ρ₀ w₀ obj w ∧ ExnRel e obj ∧ MemRel Γ.F Γ.syms cm w)

/-- **CLIF → VCode with unwinding and the ABI return values** from the driver simulation
(`iselSimU_of_driver` with `driver_correctU_abi`), for a function whose `sret` value is bound
once, also on the exceptional edges (`sretStableXB`). -/
theorem iselSimUAbi_of_driver {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {X : ExtSem} {XR : XRaise} {Γ : Rel} {env : Clif.XEnv} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A) (hds : DriverSem sem) (hRef : Refines Γ.F sem)
    (hMem : MemRefines Γ.F Γ.slotOff Γ.syms sem) (hRS : RaiseSem Γ.F X XR sem)
    (hstk : CallsStack f Γ.out) (htstk : TryStack f Γ.out) (histk : IndStack (indSigs f) Γ.out)
    (hXR : XRaiseOk env (f.externs.map (·.2)) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hXRi : XRaiseIndOk env (indSigs f) (fun sl cm w => Γ.holds f sl cm w) X XR)
    (hsym : ∀ n b, Γ.syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hS : sretStableXB f = true) :
    IselSimUAbi sem XR Γ env p f vc := by
  have HR : RaiseHyp f sem (fun sl cm w => Γ.holds f sl cm w) env Γ.F X XR Γ.slotOff Γ.syms
      Γ.out :=
    ⟨hRS, hRef, hMem, mrStable_holds Γ f, outArgsOk_holds Γ f, memRelOk_holds Γ f, hstk, htstk,
      histk, hXR, hXRi, hsym, fun sl cm w h => (memRelOk_holds Γ f).symbols sl cm w h⟩
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctU_abi H HU HR hds hB0 hce.callers hce.func rfl hbody hterm hregs
    hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs htr (Q := (· = sretArg f args))
    (sret_reachX H.ext H.tryExt H.noTail htr hS hB0 hce.callers hce.func hbody hterm hregs
      hty.symm)
    fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_, fun e cm h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, hsv, h3, h4, h5⟩ := hrun
    subst hsv
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩
  · rw [h] at hrun
    exact hrun
  · rw [h] at hrun
    obtain ⟨obj, w, cm0, hu, hex, h4, h5⟩ := hrun
    exact ⟨obj, w, hu, hex, h5 ▸ memRel_leave (memRel_free h4.1 _)⟩

/-- **CLIF → VCode with unwinding and the ABI return values for the backend's code under
`csemU`** (`iselSimU_final` with `sretStableXB f`). -/
theorem iselSimU_final_abi {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    (hS : sretStableXB f = true)
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
    IselSimUAbi (csemU F fctx X XR) XR ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ env
      p f vc := by
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
  refine iselSimUAbi_of_driver (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A)
    ?_ hUS (driverSem_csemU F fctx X XR) hRef hmem (raiseSem_csemU F fctx X XR)
    (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
    (tryStack_mono (tryStack_of_check hc.lowerOk) houtB)
    (indStack_mono (indStack_of_check hc.lowerOk) houtB) hXR hXRi hsym hS
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

/-- What the Arm run with unwinding does for a CLIF outcome with unwinding, with the ABI return
values `rets` after the CLIF ones (`ArmRefinesU` otherwise). -/
def ArmRefinesUAbi (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (rets : List Clif.Val) : Clif.XOutcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v, (vals ++ rets)[j]? = some v → XHolds v (xreg j (runX astep n s))) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .unwound e cm => ∃ n, ArmRet ra s (runX astep n s) ∧ ExnRel e (xreg 0 (runX astep n s)) ∧
      MemAgree cm (runX astep n s)
  | .stuck _ | .outOfFuel => True

theorem ArmRefinesUAbi.armRefinesU {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {rets : List Clif.Val}
    {o : Clif.XOutcome} (h : ArmRefinesUAbi fb base ra astep s rets o) :
    ArmRefinesU fb base ra astep s o := by
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hm⟩ := h
    refine ⟨n, hret, fun j v hj => hx j v ?_, hm⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
    exact hj
  | trapped c => exact h
  | unwound e cm => exact h
  | _ => trivial

/-- **Composition with unwinding and the ABI return values** (`backend_correct_of_layersU_ex`
for `IselSimUAbi`). -/
theorem backend_correct_of_layersU_ex_abi {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop} {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.XEnv}
    (hIsel : ∀ s, IselSimUAbi (sem s) XR ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrectU (sem s) XR vc vcp)
    (hReg : RegLevelCorrectUEx sem XR F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesUAbi fb base ra astep s (sretArg f args) (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨ρ₀, hR1, hR2, hR3⟩ := hReg base ra s hent hres w₀ hbe
  have hI := hIsel s args cs w₀ ρ₀ hcs hrel hargs htr fuel
  cases hrun : Clif.runLoopX env p fuel cs.toX with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR1 us outs w (((hPrep s).1 _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_of hmem hmemF⟩
    intro j v hj
    have hjv : j < (vals ++ sretArg f args).length := (List.getElem?_eq_some_iff.mp hj).1
    have hju : j < us.length := by have := hhold.1; omega
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by have := hhold.1; omega), List.getElem?_eq_getElem _⟩
    have hp : (us[j]'hju).2 = Reg.x j := by
      have := congrArg (fun l => l[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some] at this
      exact Option.some.inj this
    have hr := hregs j (us[j]'hju).1 (us[j]'hju).2 x (by simp [List.getElem?_eq_getElem hju]) hx
    rw [hp, regVal_x] at hr
    show VHolds v (ofX (xreg j (runX astep n s)))
    rw [hr]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR2 c (((hPrep s).1 _ _).2 c (hI.2.1 c hrun))
  | unwound e cm =>
    obtain ⟨obj, w, hv, hex, hmem⟩ := hI.2.2 e cm hrun
    obtain ⟨n, hret, hx0, hmemF⟩ := hR3 obj w ((hPrep s).2 _ _ _ _ hv)
    exact ⟨n, hret, by rw [hx0]; exact hex, memAgree_of hmem hmemF⟩
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The backend's end-to-end theorem with unwinding and the ABI return values, for an
`AllocChecked` allocation**: `backend_correct_final_unwind_ex` (its premises plus
`sretStableXB f`), and a return also leaves the ABI return values after the CLIF ones in x0..
(`sretArg f args`). -/
theorem backend_correct_final_unwind_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledA f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    (hS : sretStableXB f = true)
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
    ArmRefinesUAbi fb base ra (Unw.ArmStepU X H U T fa) s (sretArg f args)
      (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU_ex_abi
    (sem := fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X XR)
    (fun s' => iselSimU_final_abi hsub hc hunw hS (hX s') (hXI s') (hXR s') (hXRi s') (hXE s')
      hsym hslot)
    (fun _ => prepareCorrectU_of_check (driverSem_csemU _ _ _ _) hc.prepOk XR)
    (regLevelCorrect_backend_exU hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallA hc h)) (fun h => hTls (hasTls_of_vcodeA hc h)) hUnw
      hsites hlsda hpad hlast hrows hcie hfde hsaved)
    hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs
      (stackArgsAvoid_frameWA hc hres hent hargs))
    hcs hrel htr fuel

/-- **The backend's end-to-end theorem with unwinding and the ABI return values**
(`docs/contracts/e2e.md`, "`sret`"): `backend_correct_final_unwind` (its premises plus
`sretStableXB f`), and a return also leaves the ABI return values after the CLIF ones in x0..:
for a function with an `sret` parameter and no returns, the `sret` argument in x0 (`sretArg`,
`backend_correct_final_unwind_sret`). -/
theorem backend_correct_final_unwind_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    (hS : sretStableXB f = true)
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
    ArmRefinesUAbi fb base ra (Unw.ArmStepU X H U T fa) s (sretArg f args)
      (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_layersU_ex_abi
    (sem := fun s => csemU (frameW K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af s) ⟨fa.k, af.slotBase⟩ X XR)
    (fun s' => iselSimU_final_abi hsub hc.toA hunw hS (hX s') (hXI s') (hXR s') (hXRi s')
      (hXE s') hsym hslot)
    (fun _ => prepareCorrectU_of_check (driverSem_csemU _ _ _ _) hc.prepOk XR)
    (regLevelCorrect_backendU hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCall hc h)) (fun h => hTls (hasTls_of_vcode hc h)) hUnw
      hsites hlsda hpad hlast hrows hcie hfde hsaved).ex
    hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs
      (stackArgsAvoid_frameW hc hres hent hargs))
    hcs hrel htr fuel

/-- **The `sret` return register with unwinding**: for a function with an `sret` parameter `i`
and no returns, under the premises of `backend_correct_final_unwind_abi`, a return of the CLIF
run with unwinding is matched by an Arm return (`ArmRet`) on the machine with unwinding whose x0
holds the `sret` argument `args[i]`, with the memory the function wrote (`MemAgree`). -/
theorem backend_correct_final_unwind_sret {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hunw : unwCheck f vc = true)
    (hS : sretStableXB f = true)
    {i : Nat} (hi : f.sig.params.findIdx? (·.purpose == .sret) = some i)
    (hnr : f.sig.returns = [])
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
    (htr : TrapsExplicitX env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoopX env p fuel cs.toX = .returned vals cm) {v : Clif.Val}
    (hv : args[i]? = some v) :
    ∃ n, ArmRet ra s (runX (Unw.ArmStepU X H U T fa) n s) ∧
      XHolds v (xreg 0 (runX (Unw.ArmStepU X H U T fa) n s)) ∧
      MemAgree cm (runX (Unw.ArmStepU X H U T fa) n s) := by
  obtain ⟨B0, hentB, hbody, hterm, -, -⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hvals : vals = [] := by
    have := runLoopX_returned_tys_entry hsub.externCalls hsub.tryExterns (noTail_of_subset hsub)
      htr (sretStableX_of hS) hB0 hcs.callers hcs.func hbody hterm hrun
    rw [hnr] at this
    simpa [Clif.AbiParam.tys] using this
  subst hvals
  have h := backend_correct_final_unwind_abi hsub hc hunw hS hcov hC hCT hTls hX hXI hXR hXRi hXE
    hsym hslot hUnw hsites hlsda hpad hlast hrows hcie hfde hsaved hent hres hbe hargs hcs hrel
    htr fuel
  rw [hrun, sretArg_of_sret hi hnr, hv] at h
  obtain ⟨n, hret, hx, hm⟩ := h
  exact ⟨n, hret, hx 0 v (by simp), hm⟩

end E2E

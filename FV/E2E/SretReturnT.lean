import FV.E2E.FinalT
import FV.E2E.SretReturn

/-!
# The `sret` return register through the typed chain (S7)

The typed chain (`backend_correct_finalT` and its stages, `ArmRefinesT`) claims each CLIF return
value in the ABI return register of its class; the `_abi` copies also claim the ABI return
values after them (`sretArg f args`, as `backend_correct_final_abi`), each in the return register
of its class in the combined list (`ArmRefinesTAbi`), with the extra premise
`sretStableB f = true`:

* `IselSimTAbi`, `iselSimTAbi_of_driverT` (from `driver_correctT_abi` and `sret_reach`),
  `iselSimTAbi_of_rules`;
* `ArmRefinesTAbi` (`ArmRefinesTAbi.armRefinesT` gives back `ArmRefinesT`),
  `backend_correct_of_layers_exT_abi`, `backend_correct_of_rules_exT_abi`,
  `backend_correct_m4_exT_abi`, `backend_correct_final_exT_abi`, **`backend_correct_finalT_abi`**;
* **`backend_correct_finalT_sret`**: for a function with an integer `sret` parameter `i` and no
  returns, a CLIF return is matched by an Arm return with `args[i]` in x0.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **CLIF → VCode, typed, with the ABI return values**: `IselSimT` with the returned use values
holding the CLIF return values followed by `sretArg f args` (`AllHold`), in the return registers
of the combined list's classes (`RetRegsOk`). -/
def IselSimTAbi (sem : Sem) (Γ : Rel) (env : Clif.Env) (p : Clif.Program) (f : Clif.Function)
    (vc : VCode) : Prop :=
  ∀ args cs w₀ (ρ₀ : Nat → CV), ClifEntry f args cs → Γ.holds f cs.frame.slots cs.mem w₀ →
    ArgsAtEntry Γ.F f.sig args w₀ → TrapsExplicit env p cs → ∀ fuel,
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc sem ρ₀ w₀ us outs w ∧
        RetRegsOk (vals ++ sretArg f args) us ∧ us.length = outs.length ∧
        AllHold (vals ++ sretArg f args) outs ∧ MemRel Γ.F Γ.syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c, Clif.runLoop env p fuel cs = .trapped c → VTraps vc sem ρ₀ w₀ c)

/-- **CLIF → VCode, typed, with the ABI return values** from the typed driver simulation, for a
function whose `sret` value is bound once (`sretStableB`). -/
theorem iselSimTAbi_of_driverT {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHypT f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem)
    (hFP : MemRefinesFP (fun _ => True) Γ.F sb sem) (hS : sretStableB f = true) :
    IselSimTAbi sem Γ env p f vc := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := runPrem_of_entry hce htr
  have hrun := driver_correctT_abi H hds hMem hFP (mrStable_holds Γ f) hB0 hce.callers hce.func rfl
    hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP
    (Q := (· = sretArg f args))
    (sret_reach H.ext H.tryExt H.noTail hP hS hB0 hce.callers hce.func hbody hterm hregs hty.symm)
    fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, sv, hret, h1, h2, hsv, h3, h4, h5, h6⟩ := hrun
    subst hsv
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **What the Arm run does for a CLIF outcome, typed, with the ABI return values** `rets` after
the CLIF ones: each value of `vals ++ rets` held by the return register of its class in the
combined list (`retRegsT`). -/
def ArmRefinesTAbi (fb : FnBin) (base ra : BitVec 64) (astep : Arm.ArmState → Arm.ArmState)
    (s : Arm.ArmState) (rets : List Clif.Val) : Clif.Outcome → Prop
  | .returned vals cm => ∃ n, ArmRet ra s (runX astep n s) ∧
      (∀ (j : Nat) v r, (vals ++ rets)[j]? = some v →
        (retRegsT ((vals ++ rets).map fun v => tyClass v.ty) 0 0)[j]? = some r →
        VHolds v (regVal (runX astep n s) r)) ∧
      MemAgree cm (runX astep n s)
  | .trapped c => ∃ n, TrapAt fb base c (runX astep n s)
  | .stuck _ | .outOfFuel => True

theorem ArmRefinesTAbi.armRefinesT {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {rets : List Clif.Val}
    {o : Clif.Outcome} (h : ArmRefinesTAbi fb base ra astep s rets o) :
    ArmRefinesT fb base ra astep s o := by
  cases o with
  | returned vals cm =>
    obtain ⟨n, hret, hx, hm⟩ := h
    refine ⟨n, hret, fun j v r hj hr => hx j v r ?_ ?_, hm⟩
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
      exact hj
    · obtain ⟨rest, hrest⟩ := retRegsT_append (vals.map fun v => tyClass v.ty)
        (rets.map fun v => tyClass v.ty) 0 0
      rw [List.map_append, hrest, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1]
      exact hr
  | trapped c => exact h
  | _ => trivial

/-- **Composition, typed, with the ABI return values** (`backend_correct_of_layers_exT` for
`IselSimTAbi`). -/
theorem backend_correct_of_layers_exT_abi {p : Clif.Program} {f : Clif.Function} {vc vcp : VCode}
    {af : AFunc} {fb : FnBin} {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat}
    {astep : Arm.ArmState → Arm.ArmState} {env : Clif.Env}
    (hIsel : ∀ s, IselSimTAbi (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc)
    (hPrep : ∀ s, PrepareCorrect (sem s) vc vcp)
    (hReg : RegLevelCorrectEx sem F K astep vcp af fb)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsAtEntry (F s) f.sig args w₀)
    (hcs : ClifEntry f args cs) (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesTAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) := by
  obtain ⟨ρ₀, hR⟩ := hReg base ra s hent hres w₀ hbe
  have hI := hIsel s args cs w₀ ρ₀ hcs hrel hargs htr fuel
  cases hrun : Clif.runLoop env p fuel cs with
  | returned vals cm =>
    obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmem, -⟩ := hI.1 vals cm hrun
    obtain ⟨n, hret, hregs, hmemF⟩ := hR.1 us outs w ((hPrep s _ _).1 _ _ _ hv)
    refine ⟨n, hret, ?_, memAgree_ofT hmem hmemF⟩
    intro j v r hj hr
    obtain ⟨u, hu, hur⟩ := retRegsOk_get hus hr
    have hju : j < us.length := (List.getElem?_eq_some_iff.mp hu).1
    obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
      ⟨outs[j]'(by omega), List.getElem?_eq_getElem _⟩
    have hrv := hregs j u.1 u.2 x (by rw [hu]) hx
    rw [hur] at hrv
    rw [hrv]
    exact hhold.2 j v x hj hx
  | trapped c =>
    exact hR.2 c ((hPrep s _ _).2 c (hI.2 c hrun))
  | stuck _ => trivial
  | outOfFuel => trivial

/-- `iselSimT_of_rules` with the ABI return values (`sretStableB f`). -/
theorem iselSimTAbi_of_rules {p : Clif.Program} {f : Clif.Function} {vc : VCode}
    (hsub : InSubsetT p f) (hlow : lowerCheckT f vc = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program)
    (hcallRules : CallRulesCorrectT Isle.Aarch64.program)
    (hindRules : IndRulesCorrectT Isle.Aarch64.program)
    (hmemRules : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrectT Isle.Aarch64.program)
    (htermUn : TermUnmatchableT Isle.Aarch64.program)
    (hbranch : BranchRulesCorrectT Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchableT Isle.Aarch64.program)
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out) :
    ∀ s, IselSimTAbi (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligationsT_of_check hlow
  have hctxT : CtxT f ctx := CtxT.ofExterns hshape.ctxInvT hshape.scope (functionET_externs hsub.subsetET)
  have hstT : StoresTyped ctx :=
    storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  intro s'
  refine iselSimTAbi_of_driverT (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A)
    ?_ (hds s') (hmem s') (hFP s') hS
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCallsT_of_rules hrules hrulesF hrulesA hnE hcallRules hindRules hmemRules hmemF
      (hRef s') (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (hFP s') (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStackT_of_check hlow) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f) hctxT hshape.scope hstT
    terms := termCallsT_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetT hsub
    subET := hsub.subsetET
    entryLocs := entryOkT_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetT hsub
    tries := ⟨out, tryCallsT_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') hctxT,
      tryStack_mono (tryStackT_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s') hctxT
    tryIndSig := tryIndSig_of_subsetT hsub
    cfg := hcfg }

/-- `backend_correct_of_rules_exT` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_of_rules_exT_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program)
    (hcallRules : CallRulesCorrectT Isle.Aarch64.program)
    (hindRules : IndRulesCorrectT Isle.Aarch64.program)
    (hmemRules : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrectT Isle.Aarch64.program)
    (htermUn : TermUnmatchableT Isle.Aarch64.program)
    (hbranch : BranchRulesCorrectT Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchableT Isle.Aarch64.program)
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesTAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_of_layers_exT_abi
    (iselSimTAbi_of_rules hsub hc.lowerOk (cfg_of_prepare hc.prepare) hS hrules hrulesF hrulesA
      hnE hcallRules hindRules hmemRules hmemF
      htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn hRef hds hcalls
      hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsT_of_check hc.lowerOk) hbe hargs hargF hres)
    hcs hrel htr fuel

/-- `backend_correct_m4_exT` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_m4_exT_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    (hT : TypedRules)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hM6 : RegLevelCorrectEx (fun s => csem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (csem (F s) (ctx s) (X s)))
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (csem (F s) (ctx s) (X s)))
    (hslotB : ∀ s, (ctx s).slotBase = slotOff)
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesTAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_exT_abi hsub hc hS lowerRulesCorrectTI_program
    lowerRulesCorrectT_program
    lowerRulesCorrectFT_program nonEUnmatchableT_program hT.callsT hT.indT
    memRulesCorrectRTI_program
    memRulesCorrectRT_program hT.term
    hT.termUn hT.branch hT.branchEx hT.tryT hT.tryUn hT.tryIndT hT.tryIndUn
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun s' => memRefinesFP_csem _ (F s') (ctx s') (X s') (hslotB s')) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- `backend_correct_final_exT` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_final_exT_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesTAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_exT_abi (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc hS hT
    (regLevelCorrect_backend_ex hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallAT hc h)) (fun h => hTls (hasTls_of_vcodeAT hc h)))
    (refines_final K vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (fun _ => hslot) (outgoing_le_intBaseAT hc)
    hent hres hbe hargs (stackArgsAvoid_frameWAT hc hres hent hargs) hcs hrel htr fuel

/-- **The typed final theorem with the ABI return values**: `backend_correct_finalT` (its
premises plus `sretStableB f`), and a return also leaves the ABI return values `sretArg f args`
after the CLIF ones, each in the return register of its class in the combined list
(`ArmRefinesTAbi`; for an integer `sret` parameter and no returns, x0:
`backend_correct_finalT_sret`). -/
theorem backend_correct_finalT_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    (hT : TypedRules)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesTAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_final_exT_abi hsub hc.toA hS hT hcov hC hCT hTls hX hXI hsym hslot hent hres
    hbe hargs hcs hrel htr fuel

/-- **The `sret` return register through the typed chain**: for a function with an integer
`sret` parameter `i` and no returns, under the premises of `backend_correct_finalT_abi`, a CLIF
return is matched by an Arm return whose x0 holds the `sret` argument `args[i]`, with the memory
the function wrote (`MemAgree`). -/
theorem backend_correct_finalT_sret {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb) (hS : sretStableB f = true)
    (hT : TypedRules)
    {i : Nat} (hi : f.sig.params.findIdx? (·.purpose == .sret) = some i)
    (hint : ∀ q, f.sig.params[i]? = some q → q.ty.isInt = true)
    (hnr : f.sig.returns = [])
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) {v : Clif.Val}
    (hv : args[i]? = some v) :
    ∃ n, ArmRet ra s (runX (ArmStepX X H fa) n s) ∧
      XHolds v (xreg 0 (runX (ArmStepX X H fa) n s)) ∧
      MemAgree cm (runX (ArmStepX X H fa) n s) := by
  obtain ⟨B0, hentB, hbody, hterm, -, -⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hvals : vals = [] := by
    have := runLoop_returned_tys_entry hsub.externCalls hsub.tryExterns (noTail_of_subsetT hsub)
      (runPrem_of_entry hcs htr) (sretStable_of hS) hB0 hcs.callers hcs.func hbody hterm hrun
    rw [hnr] at this
    simpa [Clif.AbiParam.tys] using this
  subst hvals
  -- `v` is an integer: its type is the `sret` parameter's
  have hvi : v.ty.isInt = true := by
    have hsig := congrArg (fun l => l[i]?) hcs.sig
    simp only [List.getElem?_map, hv, Option.map_some] at hsig
    cases hq : f.sig.params[i]? with
    | none => rw [hq] at hsig; cases hsig
    | some q =>
      rw [hq, Option.map_some, Option.some.injEq] at hsig
      rw [hsig]; exact hint q hq
  have h := backend_correct_finalT_abi hsub hc hS hT hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel
  rw [hrun, sretArg_of_sret hi hnr, hv] at h
  obtain ⟨n, hret, hx, hm⟩ := h
  refine ⟨n, hret, ?_, hm⟩
  have hcl : tyClass v.ty = .int := by simp only [tyClass, hvi, ↓reduceIte]
  have := hx 0 v (.x 0) (by simp) (by
    simp only [List.nil_append, Option.toList_some, List.map_cons, List.map_nil, hcl]; rfl)
  rwa [regVal_x] at this

end E2E

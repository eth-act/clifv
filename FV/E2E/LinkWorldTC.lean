import FV.E2E.LinkWorldT
import FV.E2E.FinalTC
import FV.E2E.FinalTCF

/-! # The per-function theorem with the final world, typed `try_call`s (S11e6, #419)

`FV/E2E/LinkWorldT.lean` for the scope with typed direct `try_call`s (`InSubsetTC`,
`CompiledTC`), from the typed driver simulation with typed `try_call`s (`driver_correctTC`,
`LowerSimTC.lean`) and the proven `tryRulesCorrectTFP_program` family: the driver hypothesis
with the memory relation `RelW`, the per-function theorem `backend_correct_worldTC` (the same
conclusions as `backend_correct_worldT`).

S11f (#35): the theorems are proven for the scope with the proven float operations
(`InSubsetTCF`, `CompiledTCF`: `Compile.functionETCF`, validator `lowerCheckTCF`; the statement
calls from `instCallsTF_of_rules` with the conversion and `fcmp` roots), suffix `TCF`; the `TC`
theorems are their corollaries (`InSubsetTC.toTCF`, `CompiledTC.toTCF`), statements unchanged.

* `driverHypTCF_relW_of`, `driverHypTCF_relW` (`driverHypTC_relW_of`, `driverHypTC_relW`): the
  driver hypothesis with `RelW` (any semantics with the driver-level facts; at `csem`);
* `iselSim_relWTCF` (`iselSim_relWTC`): CLIF → VCode with `RelW`, returns in their classes'
  registers (`RetRegsOk`);
* `backend_correct_worldTCF` (`backend_correct_worldTC`): `backend_correct_world` with
  `RetRegsOk` and the returned values' types.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The driver hypothesis with the memory relation `RelW`, with the proven float operations**,
for any VCode semantics with the driver-level facts (every typed M4 obligation from the rule
families, with the conversion and `fcmp` roots and `NonEUnmatchableTF`; the context and
certificate of `loweringTCF_of_check`; the direct `try_call`s from the proven family
`tryRulesCorrectTFP_program`). -/
theorem driverHypTCF_relW_of {sem : Sem} (hsub : InSubsetTCF p f) (hT : TypedRules)
    (hlow : lowerCheckTCF f vc = true) (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) {out : Nat}
    (houtB : vc.outgoing ≤ out) (hRef : Refines F sem) (hds : DriverSem sem)
    (hcalls : CallsRefine F env (f.externs.map (·.2)) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hicalls : IndCallsRefine env (indSigs f) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hmem : MemRefines F slotOff syms sem) (hFP : MemRefinesFP (fun _ => True) F slotOff sem)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A sem (RelW ⟨F, syms, slotOff, out⟩ f c) env p := by
  let Γ : Rel := ⟨F, syms, slotOff, out⟩
  have hctxT : CtxT f ctx :=
    ctxT_of_functionETCF hsub.subsetETCF hshape.hctx.choose_spec hshape.ctxInvT hshape.scope
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  exact {
    shape := hshape
    cert := hcert
    dsem := hds.toDriverSemG
    insts := instCallsTF_of_rules lowerRulesCorrectTI_program lowerRulesCorrectT_program
      lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program lowerRulesCorrectFC_program
      nonEUnmatchableTF_program hT.callsT hT.indT
      memRulesCorrectRTI_program memRulesCorrectRT_program hRef (mrStable_relW Γ f c) hcalls
      hicalls hmem hFP (outArgsOk_relW Γ f c)
      (callsStack_mono (callsStackTCF_of_check hlow) houtB)
      (indStack_mono (indStackTCF_of_check hlow) houtB) (memRelOk_relW Γ f c) hctxT hstT
    terms := termCallsT_of_rules hT.term hT.termUn hT.branch hT.branchEx hRef
      (mrStable_relW Γ f c) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetTCF hsub
    subETC := hsub.subsetETCF
    entryLocs := entryOkTCF_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetTCF hsub
    tries := ⟨_, tryCallsTC_of_rules hRef (mrStable_relW Γ f c) hmem hFP
      (outArgsOk_relW Γ f c) hcalls hshape.ctxInvT,
      tryStack_mono (tryStackTCF_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules hT.tryIndT hT.tryIndUn hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) (indStack_mono (indStackTCF_of_check hlow) houtB) hicalls hctxT
    tryIndSig := tryIndSig_of_subsetTCF hsub
    cfg := hcfg }

/-- **The driver hypothesis with the memory relation `RelW`, typed `try_call`s**, for any VCode
semantics with the driver-level facts (`driverHypTCF_relW_of`). -/
theorem driverHypTC_relW_of {sem : Sem} (hsub : InSubsetTC p f) (hT : TypedRules)
    (hlow : lowerCheckTC f vc = true) (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) {out : Nat}
    (houtB : vc.outgoing ≤ out) (hRef : Refines F sem) (hds : DriverSem sem)
    (hcalls : CallsRefine F env (f.externs.map (·.2)) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hicalls : IndCallsRefine env (indSigs f) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hmem : MemRefines F slotOff syms sem) (hFP : MemRefinesFP (fun _ => True) F slotOff sem)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A sem (RelW ⟨F, syms, slotOff, out⟩ f c) env p :=
  driverHypTCF_relW_of hsub.toTCF hT (lowerCheckTCF_of_lowerCheckTC hlow) hcfg houtB hRef hds
    hcalls hicalls hmem hFP hshape hcert hbr

/-- **The driver hypothesis at `csem` with the memory relation `RelW`, with the proven float
operations.** -/
theorem driverHypTCF_relW (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCF_relW_of hsub hT hc.lowerOk (cfg_of_prepare hc.prepare)
    (outgoing_le_intBaseATCF hc.toA) (refines_csem _ _ X) (driverSem_csem F ⟨fa.k, af.slotBase⟩ X)
    (callsRefine_csem hX) (indCallsRefine_csem hXI hsym (fun _ _ _ h => h.1.1.symbols))
    (memRefines_csem _ _ X hslot hsym) (memRefinesFP_csem (fun _ => True) F _ X hslot) hshape hcert
    hbr

/-- **The driver hypothesis at `csem` with the memory relation `RelW`, typed `try_call`s.** -/
theorem driverHypTC_relW (hsub : InSubsetTC p f) (hc : CompiledTC f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTC f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTC f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCF_relW hsub.toTCF hc.toTCF hT hX hXI hsym hslot hshape hcert hbr

/-- **CLIF → VCode with the proven float operations, for `csem`** with a fixed set `F` of
addresses outside the world and the memory relation `RelW` (`iselSim_relWTC` for the scope with
the proven float operations; the returned values in their classes' return registers,
`RetRegsOk`, with the signature's return types). -/
theorem iselSim_relWTCF (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  have H := driverHypTCF_relW (c := c) hsub hc hT hX hXI hsym hslot hshape hcert hbr
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctTC H (driverSem_csem F ⟨fa.k, af.slotBase⟩ X)
    (memRefines_csem _ _ X hslot hsym) (memRefinesFP_csem (fun _ => True) F _ X hslot)
    (mrStable_relW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig
    (ρ₀ := ρ₀) hrel hargs (runPrem_of_traps hce htr) fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **CLIF → VCode, typed `try_call`s, for `csem`** with a fixed set `F` of addresses outside the
world and the memory relation `RelW` (`iselSim_relWT` for the scope with typed `try_call`s; the
returned values in their classes' return registers, `RetRegsOk`, with the signature's return
types; `iselSim_relWTCF`). -/
theorem iselSim_relWTC (hsub : InSubsetTC p f) (hc : CompiledTC f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') :=
  iselSim_relWTCF hsub.toTCF hc.toTCF hT hX hXI hsym hslot ρ₀ hce hrel hargs htr fuel

/-- **The per-function theorem with the final world, with the proven float operations**
(`backend_correct_worldTC` for the scope with the proven float operations): for a returning CLIF
run, one VCode outcome (`us`, `outs`, `w`; the returned values in their classes' return
registers, `RetRegsOk`) that every activation entered with the body-entry world `w₀` realises
(`ActRet`); for a trapping run, every such activation reaches a trap site with the code. -/
theorem backend_correct_worldTCF (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hI := iselSim_relWTCF hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
    (fun _ => 0) w₀
  have hM6 : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := regLevelCorrect_world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR, htys⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, htys, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ :=
      (hM6 H G base ra s he).1 us outs w (vReturns_gotV (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hM6 H G base ra s he).2 c' (vTraps_gotV (hP.2 c' (hI.2 c' hrun)))

/-- **The per-function theorem with the final world, typed `try_call`s**
(`backend_correct_worldT` for the scope with typed `try_call`s, `backend_correct_worldTCF`):
for a returning CLIF run, one VCode outcome (`us`, `outs`, `w`; the returned values in their
classes' return registers, `RetRegsOk`) that every activation entered with the body-entry world
`w₀` realises (`ActRet`); for a trapping run, every such activation reaches a trap site with the
code. -/
theorem backend_correct_worldTC (hsub : InSubsetTC p f) (hc : CompiledTC f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) :=
  backend_correct_worldTCF hsub.toTCF hc.toTCF hT hcov hX hXI hsym hslot hcs hrel hargs htr fuel

end

end E2E

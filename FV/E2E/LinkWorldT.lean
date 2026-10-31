import FV.E2E.FinalT
import FV.E2E.LinkWorld

/-! # The typed per-function theorem with the final world (S11e5 Stage C, slice 7)

`LinkWorld.lean` for the typed movement scope (`InSubsetT`, `CompiledT`), from the typed driver
(`driver_correctT`) with the typed rule families: the proven `lower`/memory families and the
control families `TypedRules`.

* `driverHypT_relW_of`, `driverHypT_relW`: the typed driver hypothesis with the memory relation
  `RelW` (any semantics with the driver-level facts; at `csem`);
* `iselSim_relWT`: CLIF → VCode with `RelW`, returns in their classes' registers (`RetRegsOk`);
* `backend_correct_worldT`: `backend_correct_world` with `RetRegsOk` in place of
  `us.map (·.2) = x0, x1, …`, and the returned values' types;
* `armRefinesT_of_actRet`: an `ActRet` return is an `ArmRefinesT` return.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The typed driver hypothesis with the memory relation `RelW`**, for any VCode semantics
with the driver-level facts (every typed M4 obligation from the rule families; the context and
certificate of `loweringObligationsT`). -/
theorem driverHypT_relW_of {sem : Sem} (hsub : InSubsetT p f) (hT : TypedRules)
    (hlow : lowerCheckT f vc = true) (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) {out : Nat}
    (houtB : vc.outgoing ≤ out) (hRef : Refines F sem) (hds : DriverSem sem)
    (hcalls : CallsRefine F env (f.externs.map (·.2)) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hicalls : IndCallsRefine env (indSigs f) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hmem : MemRefines F slotOff syms sem) (hFP : MemRefinesFP (fun _ => True) F slotOff sem)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeT f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypT f vc ctx st0 R gn bl A sem (RelW ⟨F, syms, slotOff, out⟩ f c) env p := by
  let Γ : Rel := ⟨F, syms, slotOff, out⟩
  have hctxT : CtxT f ctx := CtxT.ofExterns hshape.ctxInvT hshape.scope (functionET_externs hsub.subsetET)
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  exact {
    shape := hshape
    cert := hcert
    dsem := hds.toDriverSemG
    insts := instCallsT_of_rules lowerRulesCorrectTI_program lowerRulesCorrectT_program
      lowerRulesCorrectFT_program nonEUnmatchableT_program hT.callsT hT.indT
      memRulesCorrectRTI_program memRulesCorrectRT_program hRef (mrStable_relW Γ f c) hcalls
      hicalls hmem hFP (outArgsOk_relW Γ f c)
      (callsStack_mono (callsStackT_of_check hlow) houtB)
      (indStack_mono (indStackT_of_check hlow) houtB) (memRelOk_relW Γ f c) hctxT hshape.scope hstT
    terms := termCallsT_of_rules hT.term hT.termUn hT.branch hT.branchEx hRef
      (mrStable_relW Γ f c) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetT hsub
    subET := hsub.subsetET
    entryLocs := entryOkT_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetT hsub
    tries := ⟨_, tryCallsT_of_rules hT.tryT hT.tryUn hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls hctxT, tryStack_mono (tryStackT_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules hT.tryIndT hT.tryIndUn hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) (indStack_mono (indStackT_of_check hlow) houtB) hicalls hctxT
    tryIndSig := tryIndSig_of_subsetT hsub
    cfg := hcfg }

/-- **The typed driver hypothesis at `csem` with the memory relation `RelW`.** -/
theorem driverHypT_relW (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeT f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypT f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypT_relW_of hsub hT hc.lowerOk (cfg_of_prepare hc.prepare) (outgoing_le_intBaseAT hc.toA)
    (refines_csem _ _ X) (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) (callsRefine_csem hX)
    (indCallsRefine_csem hXI hsym (fun _ _ _ h => h.1.1.symbols)) (memRefines_csem _ _ X hslot hsym)
    (memRefinesFP_csem (fun _ => True) F _ X hslot) hshape hcert hbr

/-- The run premises of the driver from `TrapsExplicit` (as in `iselSim_relW`). -/
theorem runPrem_of_traps {cs : Clif.State} {args : List Clif.Val} (hce : ClifEntry f args cs)
    (htr : TrapsExplicit env p cs) : RunPrem env p f cs := by
  have hf := hce.func
  exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
      (hf ▸ hB),
    fun s c callee args et hr hs hb hT B hB =>
      htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
    fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
      htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
    fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
      htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩

/-- **CLIF → VCode, typed, for `csem`** with a fixed set `F` of addresses outside the world and
the memory relation `RelW` (`iselSim_relW` for the typed scope; the returned values in their
classes' return registers, `RetRegsOk`, with the signature's return types). -/
theorem iselSim_relWT (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
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
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligationsT_of_check hc.lowerOk
  have H := driverHypT_relW (c := c) hsub hc hT hX hXI hsym hslot hshape hcert hbr
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctT H (driverSem_csem F ⟨fa.k, af.slotBase⟩ X)
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

/-- **The typed per-function theorem with the final world** (`backend_correct_world` for the
typed scope): for a returning CLIF run, one VCode outcome (`us`, `outs`, `w`; the returned values
in their classes' return registers, `RetRegsOk`) that every activation entered with the
body-entry world `w₀` realises (`ActRet`); for a trapping run, every such activation reaches a
trap site with the code. -/
theorem backend_correct_worldT (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
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
  have hI := iselSim_relWT hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
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

end

/-- An `ActRet` return is an `ArmRefinesT` return: each returned value in its class's return
register, the live CLIF bytes (for a VCode outcome related to the CLIF one as
`backend_correct_worldT` gives it). -/
theorem armRefinesT_of_actRet {fb : FnBin} {base ra : BitVec 64}
    {astep : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {F G : BitVec 64 → Prop}
    {syms : String → Option Nat} {vals : List Clif.Val} {cm : Clif.Mem} {us : List (Reg × Reg)}
    {outs : List CV} {w : Arm.ArmState} (hus : RetRegsOk vals us)
    (hlen : us.length = outs.length) (hhold : PrefixHold vals outs) (hm : MemRel F syms cm w)
    {n : Nat} (h : ActRet ra F G us outs w s (runX astep n s)) :
    ArmRefinesT fb base ra astep s (.returned vals cm) := by
  refine ⟨n, h.ret, fun j v r hj hr => ?_, memAgree_ofT hm h.mem⟩
  obtain ⟨u, hu, hur⟩ := retRegsOk_get hus hr
  have hju : j < us.length := (List.getElem?_eq_some_iff.mp hu).1
  obtain ⟨x, hx⟩ : ∃ x, outs[j]? = some x :=
    ⟨outs[j]'(by omega), List.getElem?_eq_getElem _⟩
  have hrv := h.regs j u.1 u.2 x (by rw [hu]) hx
  rw [hur] at hrv
  rw [hrv]
  exact hhold.2 j v x hj hx

end E2E

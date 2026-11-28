import FV.E2E.LinkWorldTC
import FV.E2E.LinkWorldR
import FV.E2E.TypedRulesSR
import FV.Backend.Proof.LowerContractTCR
import FV.Backend.Proof.LowerContractTFSOR
import FV.Backend.Proof.IselCtlCallTFPR

/-!
# The per-function theorem with the final world, typed `try_call`s, at the register-guarded
semantics (#753, stage R2)

`LinkWorldTC`'s theorems for the scope with the proven float operations at `csemR P` under the
call families with registers (`IselCtlCallTFPR`, `TypedRulesSR`) and the contracts with registers:
`driverHypTCFSO_relW_ofR`, `driverHypTCFSO_relWR`, `iselSim_relWTCFR`, `backend_correct_worldTCFR`
(for `ActEntryR P`, given `RegLevelR`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64}

/-- **The driver hypothesis with the memory relation `RelW` over a scope inside `InstScopeTFLO`**
(#35: `driverHypTCFS_relW_of` with `fcopysign` and `fma` among the instructions; their roots
`lowerRulesCorrectCS_program`, `lowerRulesCorrectFM_program`), for any VCode semantics with the
driver-level facts. -/
theorem driverHypTCFSO_relW_ofR {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx)
    {sem : Sem} (hsub : InSubsetTCF p f)
    (hlow : lowerCheckTCF f vc = true) (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps)) {out : Nat}
    (houtB : vc.outgoing ≤ out) (hRef : Refines F sem) (hds : DriverSem sem)
    (hcalls : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hicalls : IndCallsRefinePR (fun _ _ _ _ => True) env (indSigs f) (RelW ⟨F, syms, slotOff, out⟩ f c) sem)
    (hmem : MemRefines F slotOff syms sem) (hFP : MemRefinesFP (fun _ => True) F slotOff sem)
    (hpool : PoolRefinesFP F sem)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTCS S f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTCS S f vc ctx st0 R gn bl A sem (RelW ⟨F, syms, slotOff, out⟩ f c) env p := by
  let Γ : Rel := ⟨F, syms, slotOff, out⟩
  have hctxT : CtxTS S f ctx := ⟨hshape.ctxInvT, hshape.scope⟩
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hfn : FmaNegYFree ctx := fmaNegYFree_of_buildCtx (Compile.fmaNegYFree_of_functionETCF
    hsub.subsetETCF) hshape.hctx.choose_spec hshape.ctxInvT
  have hTS := typedRulesS_program S
  exact {
    shape := hshape
    cert := hcert
    dsem := hds.toDriverSemG
    insts := instCallsTFSOR_of_rules hS (lowerRulesCorrectTIS_program S) lowerRulesCorrectT_program
      lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program lowerRulesCorrectFC_program
      lowerRulesCorrectCS_program lowerRulesCorrectFM_program
      (nonEUnmatchableTFSO_program hS) callRulesCorrectTFPR_program (indRulesCorrectTPRS_program S)
      (memRulesCorrectRTIS_program S) memRulesCorrectRT_program hRef (mrStable_relW Γ f c) hcalls
      hicalls hmem hFP hpool (outArgsOk_relW Γ f c)
      (callsStack_mono (callsStackTCF_of_check hlow) houtB)
      (indStack_mono (indStackTCF_of_check hlow) houtB) (memRelOk_relW Γ f c) hctxT hfn hstT
    terms := termCallsTS_of_rules S hTS.term hTS.termUn hTS.branch hTS.branchEx hRef
      (mrStable_relW Γ f c) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetTCF hsub
    subETC := hsub.subsetETCF
    entryLocs := entryOkTCF_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetTCF hsub
    tries := ⟨_, tryCallsTCR_of_rules hRef (mrStable_relW Γ f c) hmem hFP
      (outArgsOk_relW Γ f c) hcalls hshape.ctxInvT,
      tryStack_mono (tryStackTCF_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsTRS_of_rules S (tryIndRulesCorrectTPRS_program S) hTS.tryIndUn hRef
      (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) (indStack_mono (indStackTCF_of_check hlow) houtB) hicalls hctxT
    tryIndSig := tryIndSig_of_subsetTCF hsub
    cfg := hcfg }

/-- **The driver hypothesis at `csem` with the memory relation `RelW` over a scope inside
`InstScopeTFLO`** (#35: `driverHypTCFS_relW` with `fcopysign` and `fma`;
`driverHypTCFSO_relW_of`). -/
theorem driverHypTCFSO_relWR {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx)
    (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (hshape : LowerShapeTCS S f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) :
    DriverHypTCS S f vc ctx st0 R gn bl A (csemR P F ⟨fa.k, af.slotBase⟩ X)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCFSO_relW_ofR hS hsub hc.lowerOk (cfg_of_prepare hc.prepare)
    (outgoing_le_intBaseATCF hc.toA) (refines_csemR P _ _ X) (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X)
    (callsRefinePR_csemR hX hPg _) (indCallsRefinePR_csemR hXI hsym (fun _ _ _ h => h.1.1.symbols) hPi _)
    (memRefines_csem _ _ X hslot hsym).regG (memRefinesFP_csem (fun _ => True) F _ X hslot).regG
    (poolRefinesFP_csem F _ X).regG hshape hcert hbr

/-- **CLIF → VCode with the proven float operations, for `csem`** with a fixed set `F` of
addresses outside the world and the memory relation `RelW` (`iselSim_relWTC` for the scope with
the proven float operations; the returned values in their classes' return registers,
`RetRegsOk`, with the signature's return types). -/
theorem iselSim_relWTCFR (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {args : List Clif.Val} {cs : Clif.State} {w₀ : Arm.ArmState} (ρ₀ : Nat → CV)
    (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w, VReturns vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  have H := driverHypTCFSO_relWR (hPg := hPg) (hPi := hPi) (S := InstScope.tflo) (fun _ h => h) (c := c) hsub hc hX hXI
    hsym hslot hshape hcert hbr
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctTCS _ H (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X)
    (memRefines_csem _ _ X hslot hsym).regG (memRefinesFP_csem (fun _ => True) F _ X hslot).regG
    (mrStable_relW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig
    (ρ₀ := ρ₀) hrel hargs (runPrem_of_traps hce htr) fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **The per-function theorem with the final world, with the proven float operations**
(`backend_correct_worldTC` for the scope with the proven float operations): for a returning CLIF
run, one VCode outcome (`us`, `outs`, `w`; the returned values in their classes' return
registers, `RetRegsOk`) that every activation entered with the body-entry world `w₀` realises
(`ActRet`); for a trapping run, every such activation reaches a trap site with the code. -/
theorem backend_correct_worldTCFR (hM6 : RegLevelR) (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
    (hT : TypedRules) {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
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
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have hI := iselSim_relWTCFR (hPg := hPg) (hPi := hPi) hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hP := prepareCorrect_of_check (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
    (fun _ => 0) w₀
  have hRL : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := hM6.world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
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
      (hRL H G base ra s he).1 us outs w (vReturns_gotVR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · exact (hRL H G base ra s he).2 c' (vTraps_gotVR (hP.2 c' (hI.2 c' hrun)))

end

end E2E

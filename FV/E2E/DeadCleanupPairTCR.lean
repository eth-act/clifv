import FV.E2E.DeadCleanupPairTC
import FV.E2E.DeadCleanupPairTR
import FV.E2E.PairDriverTCR

/-!
# The dead-cleanup simulation and non-interference with typed `try_call`s and the proven float
operations, at the register-guarded semantics (#753, stage R2)

`DeadCleanupPairTC` at `regG P (valueSem …)`, under the typed call families with registers and
the contracts with registers (`RegCompatGot`, `RegCompatInd`):

* `driverHypTCFSO_relW_valueR`, `prepareCorrect_cleanupTCFR`, `iselSim_relW_cleanupTCFR`;
* `lowerTryOkC_pairF_valueR`, `instCalls_pair_valueTCFSOR`, `tryCalls_pair_valueTCR` and its
  `CtxTW`/`CtxTS S` forms, `termCalls_pair_valueTWR`/`TSR`, `tryIndCalls_pair_valueTWR`/`TSR`
  (transported, `ctxWR_transport`, `scopeSR_transport`);
* `vcode_ni_valueTCFR`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The driver hypothesis at `valueSem` with the memory relation `RelW` over a scope inside
`InstScopeTFLO`** (#35: `driverHypTCFS_relW_value` with `fcopysign` and `fma`;
`driverHypTCFSO_relW_of`). -/
theorem driverHypTCFSO_relW_valueR {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx)
    (hsub : InSubsetTCF p f) (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
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
    DriverHypTCS S f vc ctx st0 R gn bl A (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) env p :=
  driverHypTCFSO_relW_ofR hS hsub hc.lowerOk (cfg_of_cleanupTCF hc)
    (outgoing_le_intBaseCleanupATCF hc.toA) (refines_valueSem _ _ X).regG
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG (callsRefinePR_valueSem hX hPg)
    (indCallsRefinePR_valueSem hXI hsym (fun _ _ _ h => h.1.1.symbols) hPi)
    (memRefines_valueSem _ _ X hslot hsym).regG
    (memRefinesFP_valueSem (fun _ => True) F _ X hslot).regG
    (poolRefinesFP_valueSem F _ X).regG hshape hcert hbr

/-- The prune-then-prepare step is correct for the register-guarded `valueSem`
(`prepareCorrect_cleanupTCF` at `regG P`). -/
theorem prepareCorrect_cleanupTCFR {P : BitVec 64 → Clif.Signature → Prop}
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) :
    PrepareCorrect (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) vc vcp := by
  intro a w
  obtain ⟨hr, ht⟩ := prune_correct (vc := vc)
    (fun _ _ _ _ _ _ hp he => valueSem_pure hp (regG_sub he)) (valueSem_cmpOverwrite _ _ _).regG a w
  obtain ⟨pr, pt⟩ := prepareCorrect_of_check ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG)
    hc.prepOk a w
  exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩

/-- **CLIF → VCode with the proven float operations, for the dead-cleanup route**
(`iselSim_relW_cleanupTC` for `InSubsetTCF`/`CompiledCleanupTCF`). -/
theorem iselSim_relW_cleanupTCFR (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRules)
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
      ∃ us outs w, VReturns vc (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vc (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  have H := driverHypTCFSO_relW_valueR (S := InstScope.tflo) (hPg := hPg) (hPi := hPi) (fun _ h => h) (c := c) hsub hc hX
    hXI hsym hslot hshape hcert hbr
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hrun := driver_correctTCS _ H (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG
    (memRefines_valueSem _ _ X hslot hsym).regG (memRefinesFP_valueSem (fun _ => True) F _ X hslot).regG
    (mrStable_relW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig
    (ρ₀ := ρ₀) hrel hargs (runPrem_of_traps hce htr) fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **The guarded simulation composition of a typed `try_call` on the register-guarded value
semantics, with the float accesses** (`lowerTryOkC_pairF_value` at `regG P`). -/
theorem lowerTryOkC_pairF_valueR {P : BitVec 64 → Clif.Signature → Prop}
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkPC Rd Pc
        (regG P (valueSemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOkC (pairSem (regG P (valueSem F ctx' X))) (MRP Γ f c D) env p ctx ci info st st'
      ms := by
  subst hΓ
  exact lowerTryOkC_pair_of
    (semG := fun Rd Pc =>
      regG P (valueSemGF Γ.F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
    (fun _ _ => regG_mono fun _ _ _ _ h => valueSemGF_sub h)
    (fun fr cm => lockstep_regG
      (guardedStepF_value (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)))
    hpin key

/-- **`instCalls_pair_valueTCFSO` at the register-guarded `valueSem`.** -/
theorem instCalls_pair_valueTCFSOR {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb) (hT : TypedRulesS S)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxTS S f ctx) (hfn : FmaNegYFree ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTCF_of_check hc.lowerOk)
    (outgoing_le_intBaseCleanupATCF hc.toA)
  refine lowerInstOk_pairF_valueR hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTermTFSO hS (lowerRulesCorrectTIS_program S)
    lowerRulesCorrectT_program lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program
    lowerRulesCorrectFC_program lowerRulesCorrectCS_program lowerRulesCorrectFM_program
    (nonEUnmatchableTFSO_program hS) callRulesCorrectTFPR_program
    (indRulesCorrectTPRS_program S) (memRulesCorrectRTIS_program S) memRulesCorrectRT_program (Refines.regG refines_valueSemGF)
    (mrStable_relW Γ f c)
    (callsRefinePR_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg)
    (indCallsRefinePR_valueSemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi)
    (MemRefinesR.regG (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (MemRefinesFP.regG (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)) (PoolRefinesFP.regG poolRefinesFP_valueSemGF)
    hctx hfn (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig
    (indStack_mono (indStackTCF_of_check hc.lowerOk) (outgoing_le_intBaseCleanupATCF hc.toA))
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **`tryCalls_pair_valueTC` at the register-guarded `valueSem`.** -/
theorem tryCalls_pair_valueTCR (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryCallsTC f ctx (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := callCtxT_tryCtx hctx.inv hph data trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOfC sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  refine lowerTryOkC_pairF_valueR hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkPCR_runTerm (isem := regG P (valueSemGF F ⟨fa.k, af.slotBase⟩ X Rd Γ.syms
    (f.externs.map (·.2)) (indSigs f) c Pc)) (Refines.regG refines_valueSemGF) (mrStable_relW Γ f c)
    (MemRefinesR.regG (memRefinesR_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (MemRefinesFP.regG (memRefinesFP_valueSemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)) (outArgsOk_relW Γ f c)
    (callsRefinePR_valueSemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg) hctx'
    (externsIn_self f) hra hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
    (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok

-- **`tryCalls_pair_valueTCR` over `CtxTW` and over `CtxTS S`.**
ctxWR_transport tryCalls_pair_valueTCR => tryCalls_pair_valueTCWR
scopeSR_transport tryCalls_pair_valueTCWR => tryCalls_pair_valueTCSR

-- **`termCalls_pair_valueTR` and `tryIndCalls_pair_valueTR` over `CtxTW` and over `CtxTS S`.**
ctxWR_transport termCalls_pair_valueTR => termCalls_pair_valueTWR
ctxWR_transport tryIndCalls_pair_valueTR => tryIndCalls_pair_valueTWR
scopeSR_transport termCalls_pair_valueTWR => termCalls_pair_valueTSR
scopeSR_transport tryIndCalls_pair_valueTWR => tryIndCalls_pair_valueTSR

/-- **Non-interference of a dead-cleanup VCode run, with the proven float operations**
(`vcode_ni_value` for the scope with the proven float operations). -/
theorem vcode_ni_valueTCFR (hsub : InSubsetTCF p f)
    (hc : CompiledCleanupTCF f k vc vcp rf af fa fb)
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
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w w', VReturns vc (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        VReturns vc (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hS : ∀ ctx, InstScope.tflo.P ctx → InstScopeTFLO ctx := fun _ h => h
  have H := driverHypTCFSO_relW_valueR (S := InstScope.tflo) (hPg := hPg) (hPi := hPi) hS (c := c) hsub hc hX hXI hsym
    hslot hshape hcert hbr
  have hctxT : CtxTS InstScope.tflo f ctx := ⟨hshape.ctxInvT, hshape.scope⟩
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hfn : FmaNegYFree ctx := fmaNegYFree_of_buildCtx (Compile.fmaNegYFree_of_functionETCF
    hsub.subsetETCF) hshape.hctx.choose_spec hshape.ctxInvT
  have hmem : MemRefines F slotOff syms (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) :=
    (memRefines_valueSem _ _ X hslot hsym).regG
  have houtB := outgoing_le_intBaseCleanupATCF hc.toA
  have hTS := typedRulesS_program InstScope.tflo
  have HP : DriverHypTCS InstScope.tflo f vc ctx st0 R gn bl A
      (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))) (MRP Γ f c D) env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair_valueR P F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair_valueTCFSOR (hPg := hPg) (hPi := hPi) hS hc hTS hX hXI hsym hslot hNI hTls hctxT hfn hstT
    terms := termCalls_pair_valueTSR _ (P := P) Γ rfl hTls ⟨fa.k, af.slotBase⟩ hTS hctxT
    ext := H.ext
    indSig := H.indSig
    subETC := H.subETC
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair_valueTCSR _ hTS hX (hPg := hPg) hsym hslot hNI hTls hctxT,
      tryStack_mono (tryStackTCF_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair_valueTSR _
      (indStack_mono (indStackTCF_of_check hc.lowerOk) houtB)
      hTS hXI (hPi := hPi) hsym hNI hTls hctxT
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP := runPrem_of_traps hce htr
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2TCS _ H
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG hmem
    (memRefinesFP_valueSem (fun _ => True) F _ X hslot).regG (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : MatchT f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  intro vals cm hrun
  have hR := sim_runTCS _ HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -, -⟩ := hR
  obtain ⟨h1, h2⟩ := vRetFrom_pair hret
  exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1 h1, VRetFrom.prefix hs2 h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

end

end E2E

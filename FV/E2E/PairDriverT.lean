import FV.E2E.LinkWorldT
import FV.E2E.GuardedFPPair

/-! # Non-interference of a compiled function, typed (S11e5 Stage C, slice 7)

`PairDriver.lean` for the typed movement scope. The typed driver (`DriverHypT`) runs on pairs of
worlds (`pairSem csem`, memory relation `MRP`); its per-step facts come from the typed rule
contracts with pinned calls at the guarded semantics with the float accesses `csemGF`
(`lowerInstOkP_runTermT`, `tryOkP_runTermT`, `tryIndOkP_runTermT`), paired by
`lowerInstOk_pairF`/`lowerTryOk_pairF` (`csemGF_lockstep2`); the terminators' at `csemG`
(`guardedStep0`). The entry: `entry_step2T` (class-aware `Args`, stack-passed floats under
`MemRefinesFP`).

* `instCalls_pairT`, `termCalls_pairT`, `tryCalls_pairT`, `tryIndCalls_pairT`;
* `vcode_niT`: two body-entry worlds that agree outside `F ∪ D` return through the same `rets`
  with the same values, final worlds agreeing outside `F ∪ D`;
* `backend_correct_world_niT`: `backend_correct_worldT` with non-interference
  (`backend_correct_world_ni` for the typed scope).
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The typed statement calls on pairs of worlds** (`InstCallsT` of `pairSem`): the typed rule
contracts with pinned calls at `csemGF` on each world, paired (`lowerInstOk_pairF`). -/
theorem instCalls_pairT (hc : CompiledT f k vc vcp rf af fa fb) (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackT_of_check hc.lowerOk) (outgoing_le_intBaseAT hc.toA)
  have hIstk := indStack_mono (indStackT_of_check hc.lowerOk) (outgoing_le_intBaseAT hc.toA)
  refine lowerInstOk_pairF hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTermT lowerRulesCorrectTI_program
    lowerRulesCorrectT_program lowerRulesCorrectFT_program nonEUnmatchableT_program hT.calls
    hT.ind memRulesCorrectRTI_program memRulesCorrectRT_program refines_csemGF
    (mrStable_relW Γ f c)
    (callsRefineP_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (indCallsRefineP_csemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
    (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (memRefinesFP_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)
    hctx hsc (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig hIstk
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **The typed terminator calls on pairs of worlds** (`TermCallsT` of `pairSem`). -/
theorem termCalls_pairT {f₀ : Clif.Function} (Γ : Rel) (hΓ : Γ.F = F) (hTls : XTls F X)
    (ctx' : FnCtx) (hT : TypedRules) {ctx : Ctx} (hctx : CtxT f₀ ctx) :
    TermCallsT ctx (pairSem (csem F ctx' X)) (MRP Γ f₀ c D) := by
  intro ti t data targets out st st' tr hbt hip htl hph hvb hd hemp hrun
  have key : ∀ (Rd : BitVec 64 → Prop), LowerTermOkT
      (csemG F ctx' X Rd Γ.syms [] [] 0 (fun _ _ _ _ => False))
      (RelW Γ f₀ c) (termCtx ctx ti data) t targets st st' st'.emitted.toList := fun Rd =>
    termCallsT_of_rules hT.term hT.termUn hT.branch hT.branchEx refines_csemG
      (hΓ ▸ mrStable_relW Γ f₀ c) hctx ti t data targets out st st' tr hbt hip htl hph hvb hd hemp
      hrun
  have k0 := key (fun _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have L := key (fun b => ¬ Zof Γ.F D cm b)
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2
  subst hΓ
  have hstep := guardedStep0 (D := D) (syms := Γ.syms) hTls ctx' cm st'.emitted.toList [] []
  revert r1 r2
  cases t
  all_goals intro r1 r2
  all_goals dsimp only at r1 r2 ⊢
  all_goals first
    | (intro vals hv
       obtain ⟨hU, k1, us1, ops1, ρ1, wa, outs1, wb, hs1, h1, h2, h3, hmr1⟩ := r1 vals hv
       obtain ⟨-, k2, us2, ops2, ρ2, wa', outs2, wb', hs2, -, -, -, hmr2⟩ := r2 vals hv
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, us1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, h1, h2, h3, hmr1, hmr2, hR⟩)
    | (obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2
       obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩)
    | (refine ⟨r1.1, fun j hj => ?_⟩
       obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hmr1⟩ := r1.2 j hj
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, hmr2⟩ := r2.2 j hj
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csem Γ.F ctx' X) csemG_sub' hstep
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hmr1, hmr2, hR⟩)

/-- **The typed `try_call` calls on pairs of worlds** (`TryCallsT` of `pairSem`). -/
theorem tryCalls_pairT (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryCallsT f ctx (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd hip he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have hip' : TermIntPos (tryCtx ctx ti data trs) (.tryCall fn args et) := hip
  refine lowerTryOk_pairF hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.inv.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkP_runTermT hT.try_ hT.tryUn refines_csemGF
    (mrStable_relW Γ f c) (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
    (outArgsOk_relW Γ f c)
    (callsRefineP_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx' (externsIn_self f)
    hra hd hip' he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok

/-- **The typed `try_call_indirect` calls on pairs of worlds** (`TryIndCallsT` of `pairSem`). -/
theorem tryIndCalls_pairT (hIstk : IndStack (indSigs f) (RAFrame.compute vcp rf).intBase)
    (hT : TypedRules)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryIndCallsT f ctx (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p (indSigs f) := by
  intro ti callee args et data sig items targets info trs lo st1 out st' tr hd hip he hsig
    hph hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have hip' : TermIntPos (tryCtx ctx ti data trs) (.tryCallIndirect callee args et) := hip
  have hsd := exnTableOpnd_sig he
  refine lowerTryOk_pairF hNI hTls (Γ := Γ) rfl (fun fr cm hfr => ?_) fun Rd Pc => ?_
  · have hfg : fr.func = f := hfr.trans hctx'.inv.func
    refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), fun sg cl ar s x vals n gg rvals cm' hi' hs hc' hv
      hsy hg hgo hty => ?_⟩
    cases hi'
    rw [hfg, hsd] at hs
    cases hs
    exact ⟨rfl, ⟨.inr ⟨hsig, hty⟩, gg, rvals, cm', hg, hgo⟩, .inr ⟨_, _, _, rfl, hfg ▸ hsd, hv⟩⟩
  · obtain ⟨ms, hem, hok⟩ := tryIndOkP_runTermT hT.tryInd hT.tryIndUn refines_csemGF
      (mrStable_relW Γ f c) (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) rfl hsym)
      (outArgsOk_relW Γ f c)
      hIstk (indCallsRefineP_csemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      hctx' hd hip' he hsig hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]
    exact hok

/-- **Non-interference of a typed compiled function's VCode run** (`vcode_ni` for the typed
scope): two body-entry worlds related to the same CLIF entry, that agree outside `F ∪ D`, with
the same argument registers and stack-passed argument bytes, return (for a returning CLIF run)
through the same `rets` with the same values, final worlds that agree outside `F ∪ D`. -/
theorem vcode_niT (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
    (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
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
      ∃ us outs w w', VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        VReturns vc (csem F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligationsT_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have H := driverHypT_relW (c := c) hsub hc hT hX hXI hsym hslot hshape hcert hbr
  have hctxT : CtxT f ctx := CtxT.ofExterns hshape.ctxInvT hshape.scope (functionET_externs hsub.subsetET)
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hmem : MemRefines F slotOff syms (csem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_csem _ _ X hslot hsym
  have houtB := outgoing_le_intBaseAT hc.toA
  have HP : DriverHypT f vc ctx st0 R gn bl A (pairSem (csem F ⟨fa.k, af.slotBase⟩ X))
      (MRP Γ f c D) env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pairT hc hT hX hXI hsym hslot hNI hTls hctxT hshape.scope hstT
    terms := termCalls_pairT Γ rfl hTls ⟨fa.k, af.slotBase⟩ hT hctxT
    ext := H.ext
    indSig := H.indSig
    subET := H.subET
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pairT hT hX hsym hslot hNI hTls hctxT,
      tryStack_mono (tryStackT_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pairT
      (indStack_mono (indStackT_of_check hc.lowerOk) (outgoing_le_intBaseAT hc.toA))
      hT hXI hsym hNI hTls hctxT
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP := runPrem_of_traps hce htr
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2T H
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hmem
    (memRefinesFP_csem (fun _ => True) F _ X hslot) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : MatchT f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  intro vals cm hrun
  have hR := sim_runT HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -, -⟩ := hR
  obtain ⟨h1, h2⟩ := vRetFrom_pair hret
  exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1 h1, VRetFrom.prefix hs2 h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **The typed per-function theorem with the final world and non-interference**
(`backend_correct_world_ni` for the typed scope): as `backend_correct_worldT`, and the one VCode
outcome of the body-entry world `w₀` is realised also by every activation entered with a
body-entry world `w₀'` related to the same CLIF entry that agrees with `w₀` outside `F ∪ D` (when
the external semantics keeps the agreement: `XNI`, `XTls`), with the same argument registers and
stack-passed argument bytes, up to the addresses `F ∪ D`. -/
theorem backend_correct_world_niT (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetRegsOk vals us ∧ vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns ∧
        us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  intro vals cm hrun
  have hI := iselSim_relWT hsub hc hT hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr fuel
  have hM6 : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntry vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := regLevelCorrect_world hc.check hc.alloc hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR, htys⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, htys, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀ H G base ra s he).1 us outs w
      (vReturns_gotV (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_niT hsub hc hT hX hXI hsym hslot hNI
      hTls (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := prepareCorrect_of_check (driverSem_csem F ⟨fa.k, af.slotBase⟩ X) hc.prepOk
      (fun _ => 0) w₀'
    obtain ⟨n, h1, h2, h3, h4, h5, h6, h7⟩ := (hM6 w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

end

end E2E

import FV.E2E.PairGuardS
import FV.E2E.PairDriverF

/-!
# The guarded paired contracts from non-interference at the exterior only (SEM1 #537, #713)

`instCalls_pairD`, `tryCalls_pairD`, `tryIndCalls_pairD` (`PairDriverD.lean`) with `XNIF` (the
external semantics' non-interference at the set `F` only) and the world difference inside `F`
(`hD : ∀ a, D a → F a`): the same proofs, the step lockstep by `guardedStepF`.

* `instCalls_pairDF`, `tryCalls_pairDF`, `tryIndCalls_pairDF`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The statement calls on pairs of worlds, guarded, from `XNIF`** (`instCalls_pairD`). -/
theorem instCalls_pairDF (hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hD : ∀ a, D a → F a) (hTls : XTls F X) :
    InstCalls f (pairSemD (csem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBase hc)
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p ctx inst
        info.results st rss st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
    obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
      excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
      refines_csemG (mrStable_relW Γ f c) (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
      hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig
      (indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBase hc))
      (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst ▸ hc') he) hvb hrun
    cases hov
    rw [hemp, Array.empty_append] at hem
    rw [hem, List.toList_toArray]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hff : fr.func = f := hfr.trans hctx.func
  have L := key (fun b => ¬ Zof F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm)
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin := callPin_stepPin (env := env) (cm := cm) hff hsig
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStepF (D := D) hNI hD hTls ⟨fa.k, af.slotBase⟩ inst fr cm
    st'.emitted.toList
  have hPD := fun (i : MInst) (_ : i ∈ st'.emitted.toList) => pairSemD_of_csemG (F := F) (D := D)
    (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X) (syms := syms)
    (exts := f.externs.map (·.2)) (sigs := indSigs f) (sp0 := c)
    (Pc := StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i
  revert r1 r2
  rcases ho : instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, ρ1, w1, hs1, hres, hmr1⟩ := r1
    obtain ⟨-, ρ2, w2, hs2, -, hmr2⟩ := r2
    obtain ⟨w1', he, hp, hR⟩ := pair_fallP hstep hPD (w := q.1) (w' := q.2) hsw hs1 hs2
    have hw : w2 = w1' := by injection he
    rw [← hw] at hp hR
    exact ⟨hU, ρ1, (w1, w2), hp, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · intro hex
    obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1 hex
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2 hex
    obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stopP hstep hPD (w := q.1) (w' := q.2) hsw hs1 hs2
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩
  · trivial

/-- **The `try_call` calls on pairs of worlds, guarded, from `XNIF`** (`tryCalls_pairD`). -/
theorem tryCalls_pairDF (hc : Compiled f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hD : ∀ a, D a → F a) (hTls : XTls F X) :
    TryCalls f (pairSemD (csem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p
      (RAFrame.compute vcp rf).intBase := by
  intro ctx ti fn args et data sig items targets info trs lo st1 out st' tr hctx hra hd he hph
    hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.call fn args) info { st1 with emitted := #[] } st'
        st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryOkP_runTerm tryRulesCorrectP tryUnmatchable refines_csemG
      (mrStable_relW Γ f c) (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym) (outArgsOk_relW Γ f c)
      (callsRefineP_csemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx' (externsIn_self f) hra hd he hi
      hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hff : fr.func = f := hfr.trans hctx'.func
  have L := key (fun b => ¬ Zof F D cm b)
    (StepPin env (f.externs.map (·.2)) (indSigs f) (.call fn args) fr cm)
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin := callPin_stepPin (env := env) (cm := cm) (inst := .call fn args) hff
    (fun _ _ _ _ h => by cases h)
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStepF (D := D) hNI hD hTls ⟨fa.k, af.slotBase⟩ (.call fn args) fr cm
    (tryFix info st'.emitted.toList)
  have hPD := fun (i : MInst) (_ : i ∈ tryFix info st'.emitted.toList) =>
    pairSemD_of_csemG (F := F) (D := D) (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X)
      (syms := syms) (exts := f.externs.map (·.2)) (sigs := indSigs f) (sp0 := c)
      (Pc := StepPin env (f.externs.map (·.2)) (indSigs f) (.call fn args) fr cm) i
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.call fn args) with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stopP hstep hPD (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

/-- **The `try_call_indirect` calls on pairs of worlds, guarded, from `XNIF`**
(`tryIndCalls_pairD`). -/
theorem tryIndCalls_pairDF (hc : Compiled f k vc vcp rf af fa fb)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hD : ∀ a, D a → F a) (hTls : XTls F X) :
    TryIndCalls (pairSemD (csem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p (indSigs f) := by
  intro g ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    hph hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (csemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
        { st1 with emitted := #[] } st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable
      refines_csemG (mrStable_relW Γ f c)
      (memRefinesR_csemG (ctx := ⟨fa.k, af.slotBase⟩) rfl hsym) (outArgsOk_relW Γ f c)
      (indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBase hc))
      (indCallsRefineP_csemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      hctx' hd he hsig hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hfg : fr.func = g := hfr.trans hctx'.func
  have hsd := exnTableOpnd_sig he
  let Pc := StepPin env (f.externs.map (·.2)) (indSigs f) (.callIndirect et.sig callee args) fr cm
  have L := key (fun b => ¬ Zof F D cm b) Pc
  have hII : InitIn (fun b => ¬ Zof F D cm b) cm := initIn_zof (Γ := Γ) hm1 D
  have hpin : CallPin Pc env (.callIndirect et.sig callee args) fr cm := by
    refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), fun sg cl ar s x vals n gg rvals cm' hi' hs hc' hv
      hsy hg hgo hty => ?_⟩
    cases hi'
    rw [hfg, hsd] at hs
    cases hs
    exact ⟨rfl, ⟨.inr ⟨hsig, hty⟩, gg, rvals, cm', hg, hgo⟩, .inr ⟨_, _, _, rfl, hfg ▸ hsd, hv⟩⟩
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1 hII hpin
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2 hII hpin
  have hstep := guardedStepF (D := D) hNI hD hTls ⟨fa.k, af.slotBase⟩
    (.callIndirect et.sig callee args) fr cm (tryFix info st'.emitted.toList)
  have hPD := fun (i : MInst) (_ : i ∈ tryFix info st'.emitted.toList) =>
    pairSemD_of_csemG (F := F) (D := D) (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X)
      (syms := syms) (exts := f.externs.map (·.2)) (sigs := indSigs f) (sp0 := c) (Pc := Pc) i
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.callIndirect et.sig callee args) with ⟨vals, cm'⟩ | c0 | m <;>
    intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stopP hstep hPD (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

end

end E2E

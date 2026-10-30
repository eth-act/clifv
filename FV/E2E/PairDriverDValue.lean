import FV.E2E.PairDriverF
import FV.E2E.DeadCleanupPair
import FV.E2E.RegLevelValueGS

/-!
# The paired contracts of the value semantics with the reads guarded (SEM1 #537, cleanup path)

`instCalls_pairD`, `termCalls_pairD`, `tryCalls_pairD`, `tryIndCalls_pairD` (`PairDriverD.lean`)
for the cleanup path's value semantics: the guarded paired semantics
`pairSemD (valueSem F ctx X) F ctx X`. The two guarded value runs (`valueSemG` at the read guard
`¬ Zof F D cm`, `DeadCleanupPair.lean`) are paired by `pair_fallP`/`pair_stopP` into `pairSemD`
(`pairSemD_of_valueSemG`: a specification form reads no memory, the other forms carry `csemG`'s
pair guard). The per-step lockstep of the two guarded runs is a premise (`StepLockV`), given by
`XNI` (`stepLockV_of_xni`, `guardedStep_value`) or by `XNIF` with the world difference inside `F`
(`stepLockV_of_xnif`, `guardedStepNIF_value`), so both pair drivers share these proofs.

* `pairSemD_of_valueSemG`, `driverSemG_pairD_value`, `guardedStepNIF_value`, `StepLockV`,
  `stepLockV_of_xni`, `stepLockV_of_xnif`;
* `instCalls_pairD_value`, `termCalls_pairD_value`, `tryCalls_pairD_value`,
  `tryIndCalls_pairD_value`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The guarded paired value step** from two `valueSemG` steps at the read guard
`¬ Zof F D cm` on worlds that agree outside `Zof F D cm`, with the same outputs and control. -/
theorem pairSemD_of_valueSemG {F D : BitVec 64 → Prop} {cm : Clif.Mem} {ctx : FnCtx}
    {X : ExtSem} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    (i : MInst) (us : List CV) (w w' : Arm.ArmState) (o : List CV) (w₁ : Arm.ArmState) (c : Ctl)
    (w₁' : Arm.ArmState) (hw : SameWorld (Zof F D cm) w w')
    (h : valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w =
      some (o, w₁, c))
    (h' : valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w' =
      some (o, w₁', c)) :
    pairSemD (valueSem F ctx X) F ctx X i us (w, w') = some (o, (w₁, w₁'), c) := by
  by_cases hp : specForm i = true
  · rw [pairSemD_of (pGuard_noLoad (specForm_loadForm hp) _ _)]
    exact pairSem_eq (valueSemG_sub h) (valueSemG_sub h')
  · have hc : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w =
        some (o, w₁, c) := by
      simpa [valueSemG, hp] using h
    have hc' : csemG F ctx X (fun b => ¬ Zof F D cm b) syms exts sigs sp0 Pc i us w' =
        some (o, w₁', c) := by
      simpa [valueSemG, hp] using h'
    rw [pairSemD_of (pGuard_of_csemG hw hc hc')]
    exact pairSem_eq (valueSemG_sub h) (valueSemG_sub h')

/-- **The guarded paired value semantics satisfies the driver's world-independent facts.** -/
theorem driverSemG_pairD_value (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    DriverSemG (pairSemD (valueSem F ctx X) F ctx X) where
  jump := fun l q => by
    rw [pairSemD_of (pGuard_noLoad rfl _ _)]
    exact (driverSemG_pair_value F ctx X).jump l q
  rename := by
    intro g gn hg i
    funext us q
    have e := (driverSemG_pair_value F ctx X).rename g gn hg i
    by_cases hP : PGuard F ctx X i us q
    · rw [pairSemD_of hP, pairSemD_of ((pGuard_rename g gn hg i us q).2 hP), e]
    · simp only [pairSemD, hP, mt (pGuard_rename g gn hg i us q).1 hP, ↓reduceIte]
  retarget := by
    intro i ls i' h
    funext us q
    have e := (driverSemG_pair_value F ctx X).retarget i ls i' h
    by_cases hP : PGuard F ctx X i us q
    · rw [pairSemD_of hP, pairSemD_of ((pGuard_retarget h us q).2 hP), e]
    · simp only [pairSemD, hP, mt (pGuard_retarget h us q).1 hP, ↓reduceIte]

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The paired lockstep of the guarded value runs of one step from `XNIF`**, the world
difference inside `F` (`guardedStep_value` with `callLockstepF`). -/
theorem guardedStepNIF_value
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X)
    (hD : ∀ a, D a → F a) (hTls : XTls F X) (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame)
    (cm : Clif.Mem) (ms : List MInst) :
    ∀ i ∈ ms, ∀ us w w' o w₁ ct o' w₁' ct', SameWorld (Zof F D cm) w w' →
      valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
      valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
        (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
      o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁' := by
  intro i _ us w w' o w₁ ct o' w₁' ct' hw h h'
  have hFZ : ∀ a, F a → Zof F D cm a := fun a h => .inl h
  exact valueSemG_lockstep2 hFZ hw (callLockstepF hNI (zof_iff_of_sub hD cm) hw)
    (fun n => hTls _ n w w' hFZ hw) h h'

/-- **The per-step paired lockstep of the guarded value runs** at the step sets `Zof F D cm`
(the premise of the value pair contracts; `stepLockV_of_xni`, `stepLockV_of_xnif`). -/
def StepLockV (F D : BitVec 64 → Prop) (syms : String → Option Nat) (X : ExtSem)
    (env : Clif.Env) (f : Clif.Function) (c : BitVec 64) : Prop :=
  ∀ (ctx : FnCtx) (inst : Clif.Inst) (fr : Clif.Frame) (cm : Clif.Mem) (i : MInst)
    (us : List CV) (w w' : Arm.ArmState) (o : List CV) (w₁ : Arm.ArmState) (ct : Ctl)
    (o' : List CV) (w₁' : Arm.ArmState) (ct' : Ctl), SameWorld (Zof F D cm) w w' →
    valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
      (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w = some (o, w₁, ct) →
    valueSemG F ctx X (fun b => ¬ Zof F D cm b) syms (f.externs.map (·.2)) (indSigs f) c
      (StepPin env (f.externs.map (·.2)) (indSigs f) inst fr cm) i us w' = some (o', w₁', ct') →
    o = o' ∧ ct = ct' ∧ SameWorld (Zof F D cm) w₁ w₁'

theorem stepLockV_of_xni
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    StepLockV F D syms X env f c :=
  fun ctx inst fr cm i => guardedStep_value (D := D) hNI hTls ctx inst fr cm [i] i
    List.mem_cons_self

theorem stepLockV_of_xnif
    (hNI : XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hD : ∀ a, D a → F a) (hTls : XTls F X) :
    StepLockV F D syms X env f c :=
  fun ctx inst fr cm i => guardedStepNIF_value hNI hD hTls ctx inst fr cm [i] i
    List.mem_cons_self

/-- **The statement calls on pairs of worlds, value semantics, guarded** (`instCalls_pairD` for
`pairSemD (valueSem …)`). -/
theorem instCalls_pairD_value (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) (hLS : StepLockV F D syms X env f c) :
    InstCalls f (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA hc.toA)
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc
        (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p ctx inst
        info.results st rss st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
    obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkP_runTerm lowerRulesCorrect_program
      excludedUnmatchable callRulesCorrectP indRulesCorrectP memRulesCorrectR_program
      refines_valueSemG (mrStable_relW Γ f c)
      (callsRefineP_valueSemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      (indCallsRefineP_valueSemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
      hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig
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
  have hstep : ∀ i ∈ st'.emitted.toList, _ := fun i _ => hLS ⟨fa.k, af.slotBase⟩ inst fr cm i
  have hPD := fun (i : MInst) (_ : i ∈ st'.emitted.toList) => pairSemD_of_valueSemG (F := F)
    (D := D) (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X) (syms := syms)
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

/-- **The terminator calls on pairs of worlds, value semantics, guarded.** -/
theorem termCalls_pairD_value {f₀ : Clif.Function} (Γ : Rel) (hΓ : Γ.F = F) (hTls : XTls F X)
    (ctx' : FnCtx) : TermCalls (pairSemD (valueSem F ctx' X) F ctx' X) (MRP Γ f₀ c D) := by
  intro f ctx ti t data targets out st st' tr hctx hbt htl hph hvb hd hemp hrun
  have key : ∀ (Rd : BitVec 64 → Prop), LowerTermOk
      (valueSemG F ctx' X Rd Γ.syms [] [] 0 (fun _ _ _ _ => False))
      (RelW Γ f₀ c) (termCtx ctx ti data) t targets st st' st'.emitted.toList := fun Rd =>
    termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable refines_valueSemG (hΓ ▸ mrStable_relW Γ f₀ c) f ctx ti t data
      targets out st st' tr hctx hbt htl hph hvb hd hemp hrun
  have k0 := key (fun _ => True)
  refine ⟨k0.mono, k0.defs, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have L := key (fun b => ¬ Zof Γ.F D cm b)
  have r1 := L.run fr cm ρ q.1 hfr hvh hdfg hm1
  have r2 := L.run fr cm ρ q.2 hfr hvh hdfg hm2
  subst hΓ
  have hstep := guardedStep0_value (D := D) (syms := Γ.syms) hTls ctx' cm st'.emitted.toList [] []
  have hPD := fun (i : MInst) (_ : i ∈ st'.emitted.toList) => pairSemD_of_valueSemG (F := Γ.F)
    (D := D) (cm := cm) (ctx := ctx') (X := X) (syms := Γ.syms) (exts := []) (sigs := [])
    (sp0 := 0) (Pc := fun _ _ _ _ => False) i
  revert r1 r2
  cases t
  all_goals intro r1 r2
  all_goals dsimp only at r1 r2 ⊢
  all_goals first
    | (intro vals hv
       obtain ⟨hU, k1, us1, ops1, ρ1, wa, outs1, wb, hs1, h1, h2, h3, hmr1⟩ := r1 vals hv
       obtain ⟨-, k2, us2, ops2, ρ2, wa', outs2, wb', hs2, -, -, -, hmr2⟩ := r2 vals hv
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stopP hstep hPD
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, us1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, h1, h2, h3, hmr1, hmr2, hR⟩)
    | (obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2
       obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stopP hstep hPD
         (w := q.1) (w' := q.2) hsw hs1 hs2
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩)
    | (refine ⟨r1.1, fun j hj => ?_⟩
       obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hmr1⟩ := r1.2 j hj
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, hmr2⟩ := r2.2 j hj
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stopP hstep hPD
         (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hmr1, hmr2, hR⟩)

/-- **The `try_call` calls on pairs of worlds, value semantics, guarded.** -/
theorem tryCalls_pairD_value (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff) (hLS : StepLockV F D syms X env f c) :
    TryCalls f (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
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
        (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p
        (tryCtx ctx ti data trs) (.call fn args) info { st1 with emitted := #[] } st'
        st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryOkP_runTerm tryRulesCorrectP tryUnmatchable refines_valueSemG
      (mrStable_relW Γ f c) (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)
      (outArgsOk_relW Γ f c)
      (callsRefineP_valueSemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1)) hctx'
      (externsIn_self f) hra hd he hi
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
  have hstep : ∀ i ∈ tryFix info st'.emitted.toList, _ := fun i _ =>
    hLS ⟨fa.k, af.slotBase⟩ (.call fn args) fr cm i
  have hPD := fun (i : MInst) (_ : i ∈ tryFix info st'.emitted.toList) =>
    pairSemD_of_valueSemG (F := F) (D := D) (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X)
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

/-- **The `try_call_indirect` calls on pairs of worlds, value semantics, guarded.** -/
theorem tryIndCalls_pairD_value
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hLS : StepLockV F D syms X env f c) :
    TryIndCalls (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X)
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p (indSigs f) := by
  intro g ctx ti callee args et data sig items targets info trs lo st1 out st' tr hctx hd he hsig
    h8 hph hinfo hregs hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hctx' := ctxInv_tryRegs (ctxInv_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)
        (RelW Γ f c) env p
        (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
        { st1 with emitted := #[] } st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryIndOkP_runTerm tryIndRulesCorrectP tryIndUnmatchable
      refines_valueSemG (mrStable_relW Γ f c)
      (indCallsRefineP_valueSemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1))
      hctx' hd he hsig h8 hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
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
  have hstep : ∀ i ∈ tryFix info st'.emitted.toList, _ := fun i _ =>
    hLS ⟨fa.k, af.slotBase⟩ (.callIndirect et.sig callee args) fr cm i
  have hPD := fun (i : MInst) (_ : i ∈ tryFix info st'.emitted.toList) =>
    pairSemD_of_valueSemG (F := F) (D := D) (cm := cm) (ctx := ⟨fa.k, af.slotBase⟩) (X := X)
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

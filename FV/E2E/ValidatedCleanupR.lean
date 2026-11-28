import FV.E2E.ValidatedCleanup
import FV.E2E.DeadCleanupWorldXR
import FV.E2E.DeadCleanupPairR
import FV.E2E.DeadCleanupWorldR

/-!
# The validated cleanup-stage Stock artifact at the register-guarded semantics (#753, stage R2)

`ValidatedCleanup` at `regG P (valueSem …)`, under the contracts with registers (`RegCompatGot`,
`RegCompatInd`), as `DeadCleanupWorldR`/`DeadCleanupPairR`/`DeadCleanupWorldXR` for
`CompiledCleanupValidated`: `iselSim_relW_cleanup_validated_ofR`,
`iselSim_relW_cleanup_validated_stageR`, `instCalls_pair_value_validatedR`,
`tryCalls_pair_value_validatedR`, `tryIndCalls_pair_value_validatedR`,
`vcode_ni_value_validated_ofR`, `vcode_ni_value_validated_stageR`, and for activations with the
register-guarded callee contracts (`ActEntryR P`), given M6 for the register-guarded semantics
(`RegLevelR`), `backend_correct_worldX_cleanup_validatedR`,
`backend_correct_world_niX_cleanup_validatedR`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- `iselSim_relW_cleanup` for `vcK`, the lowering `vc` or its kept code (`SkipHyp`), from the
lowering obligations of `vc` for the deletion's renaming and lowering record. -/
theorem iselSim_relW_cleanup_validated_ofR {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcK vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {drop : Nat → Nat → Bool}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
      ∃ us outs w, VReturns vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ c') := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) := (refines_valueSem _ _ X).regG
  have hmem : MemRefines F slotOff syms (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) :=
    (memRefines_valueSem _ _ X hslot hsym).regG
  have hcalls := callsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hPg
  have hicalls := indCallsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hPi
  have houtB := outgoing_le_intBaseCleanupA_validated hc.toCompiledCleanupValidatedA
  have H : DriverHyp f vc ctx st0 R gn bl A (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG).toDriverSemG
    insts := instCallsR_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrectPR
      indRulesCorrectPR memRulesCorrectR_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCallsR_of_rules tryRulesCorrectPR tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsR_of_rules tryIndRulesCorrectPR tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have hrun := driver_correct_stage H hsk ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG) hmem
    (mrStable_relW Γ f c) hB0 hce.callers hce.func rfl hbody hterm
    hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c' h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1.1 _)⟩
  · rw [h] at hrun
    exact hrun

/-- **`iselSim_relW_cleanup` for the code after the skip of unused instructions**
(`skipStage f vc`, which the cleanup stage prunes and prepares). -/
theorem iselSim_relW_cleanup_validated_stageR {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
      ∃ us outs w, VReturns (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      VTraps (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ c') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  exact iselSim_relW_cleanup_validated_ofR (hPg := hPg) (hPi := hPi) hsub hc hshape hcert hbr hsk hX hXI hsym hslot ρ₀ hce hrel hargs
    htr fuel

/-- **The statement calls on pairs of worlds** (`InstCalls` of `pairSem`): from the rule contracts
on each world (guarded semantics, per CLIF step), paired. -/
theorem instCalls_pair_value_validatedR (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
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
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    InstCalls f (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ctx ii info inst st rss st' tr hctx hmem hE hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA_validated hc.toCompiledCleanupValidatedA)
  have hIstk := indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA_validated hc.toCompiledCleanupValidatedA)
  have key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc
        (regG P (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)) (RelW Γ f c)
        env p ctx inst
        info.results st rss st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨B, hB, stm, hstm, hst⟩ := hmem
    obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTerm lowerRulesCorrect_program
      excludedUnmatchable callRulesCorrectPR indRulesCorrectPR memRulesCorrectR_program
      (Refines.regG refines_valueSemG) (mrStable_relW Γ f c) (callsRefinePR_valueSemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg)
      (indCallsRefinePR_valueSemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi) (MemRefinesR.regG (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
      hctx (outArgsOk_relW Γ f c) (externsIn_self f) hE (memRelOk_relW Γ f c) hi hcl hsig hIstk
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
  have hstep := guardedStep_value (D := D) hNI hTls ⟨fa.k, af.slotBase⟩ inst fr cm
    st'.emitted.toList
  revert r1 r2
  rcases ho : instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, ρ1, w1, hs1, hres, hmr1⟩ := r1
    obtain ⟨-, ρ2, w2, hs2, -, hmr2⟩ := r2
    obtain ⟨w1', he, hp, hR⟩ := pair_fall (sem := regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (regG_mono csemG_sub'_value) (lockstep_regG hstep)
      (w := q.1) (w' := q.2) hsw hs1 hs2
    have hw : w2 = w1' := by injection he
    rw [← hw] at hp hR
    exact ⟨hU, ρ1, (w1, w2), hp, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · intro hex
    obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1 hex
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2 hex
    obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (regG_mono csemG_sub'_value) (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩
  · trivial

/-- **The `try_call` calls on pairs of worlds** (`TryCalls` of `pairSem`). -/
theorem tryCalls_pair_value_validatedR
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryCalls f (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)))
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
        (regG P (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.call fn args) info { st1 with emitted := #[] } st'
        st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryOkPR_runTerm tryRulesCorrectPR tryUnmatchable (Refines.regG refines_valueSemG)
      (mrStable_relW Γ f c) (MemRefinesR.regG (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym)) (outArgsOk_relW Γ f c)
      (callsRefinePR_valueSemG hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg) hctx' (externsIn_self f) hra hd he hi
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
  have hstep := guardedStep_value (D := D) hNI hTls ⟨fa.k, af.slotBase⟩ (.call fn args) fr cm
    (tryFix info st'.emitted.toList)
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.call fn args) with ⟨vals, cm'⟩ | c0 | m <;> intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (regG_mono csemG_sub'_value) (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

/-- **The `try_call_indirect` calls on pairs of worlds** (`TryIndCalls` of `pairSem`). -/
theorem tryIndCalls_pair_value_validatedR (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X) :
    TryIndCalls (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)))
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
        (regG P (valueSemG F ⟨fa.k, af.slotBase⟩ X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc)) (RelW Γ f c)
        env p
        (tryCtx ctx ti data trs) (.callIndirect et.sig callee args) info
        { st1 with emitted := #[] } st' st'.emitted.toList := by
    intro Rd Pc
    obtain ⟨ms, hem, hok⟩ := tryIndOkPR_runTerm tryIndRulesCorrectPR tryIndUnmatchable
      (Refines.regG refines_valueSemG) (mrStable_relW Γ f c)
      (MemRefinesR.regG (memRefinesR_valueSemG (ctx := ⟨fa.k, af.slotBase⟩) rfl hsym)) (outArgsOk_relW Γ f c)
      (indStack_mono (indStack_of_check hc.lowerOk) (outgoing_le_intBaseCleanupA_validated hc.toCompiledCleanupValidatedA))
      (indCallsRefinePR_valueSemG hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi)
      hctx' hd he hsig hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]; exact hok
  have k0 := key (fun _ => True) (fun _ _ _ _ => True)
  refine ⟨k0.mono, k0.shape, fun fr cm ρ q hfr hvh hdfg hmr => ?_⟩
  obtain ⟨hm1, hm2, hsw⟩ := hmr
  have hfg : fr.func = g := hfr.trans hctx'.func
  have hsd := Backend.exnTableOpnd_sig he
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
  have hstep := guardedStep_value (D := D) hNI hTls ⟨fa.k, af.slotBase⟩
    (.callIndirect et.sig callee args) fr cm (tryFix info st'.emitted.toList)
  revert r1 r2
  rcases ho : instOutcome env p fr cm (.callIndirect et.sig callee args) with ⟨vals, cm'⟩ | c0 | m <;>
    intro r1 r2
  · obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hres, hmr1⟩ := r1
    obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, -, hmr2⟩ := r2
    obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (regG_mono csemG_sub'_value) (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
    injection he with _ _ _ _ hwa _ hwb
    rw [← hwa, ← hwb] at hp
    rw [← hwb] at hR
    exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hres, hmr1, hmr2,
      sameWorld_zof hmr1.1.1 hmr2.1.1 hR (zof_sub cm)⟩
  · trivial
  · trivial

/-- `vcode_ni_value` for `vcK`, the lowering `vc` or its kept code (`SkipHyp`), from the lowering
obligations of `vc`. -/
theorem vcode_ni_value_validated_ofR {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcK vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {drop : Nat → Nat → Bool}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
      ∃ us outs w w', VReturns vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        VReturns vcK (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) := (refines_valueSem _ _ X).regG
  have hmem : MemRefines F slotOff syms (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) :=
    (memRefines_valueSem _ _ X hslot hsym).regG
  have hcalls := callsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX hPg
  have hicalls := indCallsRefinePR_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols) hPi
  have houtB := outgoing_le_intBaseCleanupA_validated hc.toCompiledCleanupValidatedA
  have H : DriverHyp f vc ctx st0 R gn bl A (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (RelW Γ f c) env p := {
    shape := hshape
    cert := hcert
    dsem := ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG).toDriverSemG
    insts := instCallsR_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrectPR
      indRulesCorrectPR memRulesCorrectR_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCallsR_of_rules tryRulesCorrectPR tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsR_of_rules tryIndRulesCorrectPR tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hmem (outArgsOk_relW Γ f c) (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }
  have HP : DriverHyp f vc ctx st0 R gn bl A (pairSem (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X))) (MRP Γ f c D)
      env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair_valueR P F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair_value_validatedR (hPg := hPg) (hPi := hPi) hc hX hXI hsym hslot hNI hTls
    terms := termCalls_pair_valueR Γ rfl hTls ⟨fa.k, af.slotBase⟩
    ext := H.ext
    indSig := H.indSig
    subE := H.subE
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair_value_validatedR (hPg := hPg) hX hsym hslot hNI hTls,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair_value_validatedR (hPi := hPi) hc hXI hsym hNI hTls
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2Z H
    ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG) hmem (mrStable_relW Γ f c) hB0 hce.callers hce.func
    rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmkP : ∀ {ρ : Nat → CV} {w w' : Arm.ArmState},
      Match f ctx R gn bl A (RelW Γ f c) cs.frame.slots cs ⟨0, kk, ρ, w⟩ →
      Match f ctx R gn bl A (RelW Γ f c) cs.frame.slots cs ⟨0, kk, ρ, w'⟩ →
      SameWorld F w w₀ → SameWorld F w' w₀' →
      Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ, (w, w')⟩ := by
    intro ρ w w' hm1 hm2 hsw1 hsw2
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w w' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  have hmP := hmkP hm1 hm2 hsw1 hsw2
  intro vals cm hrun
  rcases hsk with rfl | hK
  · have hR := sim_run HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
    rw [hrun] at hR
    obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -⟩ := hR
    obtain ⟨h1, h2⟩ := vRetFrom_pair hret
    exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1.star h1, VRetFrom.prefix hs2.star h2,
      SameWorld.mono (zof_sub cm0) hmr.2.2⟩
  · have hkk := entry_pos hB0 hbody hm1
    -- the kept entry code has no load of an unused stack-passed parameter (#586)
    obtain ⟨ρK, ρF, wK, wK', hs1K, hm1K, hsw1K, hs2K, hm2K, hsw2K, hag⟩ := entry_matchK2 H hK
      ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG) hmem (mrStable_relW Γ f c) hB0 hce.callers
      hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
    rw [← hkk] at hs1K hm1K hs2K hm2K
    have hR := sim_run_abiK hK HP hP (Q := fun _ => True) (fun _ _ _ _ => trivial) fuel cs
      ⟨0, kidx (skipMask f R bl vc drop 0) kk, ρK, (wK, wK')⟩ (.refl _)
      ⟨⟨0, kk, ρF, (wK, wK')⟩, ⟨rfl, rfl, rfl, hag⟩, hmkP hm1K hm2K hsw1K hsw2K⟩
    rw [hrun] at hR
    obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -⟩ := hR.runOk
    obtain ⟨h1, h2⟩ := vRetFrom_pair hret
    exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1K h1, VRetFrom.prefix hs2K h2,
      SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **`vcode_ni_value` for the code after the skip of unused instructions** (`skipStage f vc`). -/
theorem vcode_ni_value_validated_stageR {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
      ∃ us outs w w', VReturns (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀ us outs w ∧
        VReturns (skipStage f vc) (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  exact vcode_ni_value_validated_ofR (hPg := hPg) (hPi := hPi) hsub hc hshape hcert hbr hsk hX hXI hsym hslot hNI hTls ρ₀ hce hrel hrel'
    hargs hsw hreg hstk htr fuel

theorem backend_correct_worldX_cleanup_validatedR (hM6 : RegLevelR) {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s) ∧
          (∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
            (runX (ArmStepX X H fa) i s)) ∧
          ∀ m, Arm.r .ERR (runX (ArmStepX X H fa) (n + m + 1) s) ≠ .None) := by
  have hPrep : PrepareCorrect (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (skipStage f vc) vcp := by
    intro a w
    obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc)
      (fun _ _ _ _ _ _ hp he => valueSem_pure hp (regG_sub he)) (valueSem_cmpOverwrite _ _ _).regG a w
    obtain ⟨pr, pt⟩ := prepareCorrect_of_check ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG)
      hc.prepOk a w
    exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
  have hI := iselSim_relW_cleanup_validated_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hP := hPrep
    (fun _ => 0) w₀
  have hRL : ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
      ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ := fun H G base ra s he => by
    have h := hM6.worldX_value hc.checkAlloc hc.alloc hc.emit hc.layout (X := X) (H := H)
      (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
      (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
      (fun _ => 0)
    rw [he.hF] at h
    exact h
  refine ⟨fun vals cm hrun => ?_, fun c' hrun H G base ra s he => ?_⟩
  · obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
    have hrs : vc.RetsSite us := by
      obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
      exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
    refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_⟩
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ :=
      (hRL H G base ra s he).1 us outs w (vReturns_gotV_valueR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · exact (hRL H G base ra s he).2 c' (vTraps_gotV_valueR (hP.2 c' (hI.2 c' hrun)))

/-- **`backend_correct_world_ni` with the per-state facts of the run** (both the ordinary and the
non-interference activations). -/
theorem backend_correct_world_niX_cleanup_validatedR (hM6 : RegLevelR) {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupValidated f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
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
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n ∧
            ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
              (runX (ArmStepX X H fa) i s)) ∧
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
            ActEntryR P vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n ∧
              ∀ i < n, actGoodX vcp rf af fa fb base s X H K G (GotV vcp)
                (runX (ArmStepX X H fa) i s)) := by
  intro vals cm hrun
  have hPrep : PrepareCorrect (regG P (valueSem F ⟨fa.k, af.slotBase⟩ X)) (skipStage f vc) vcp := by
    intro a w
    obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc)
      (fun _ _ _ _ _ _ hp he => valueSem_pure hp (regG_sub he)) (valueSem_cmpOverwrite _ _ _).regG a w
    obtain ⟨pr, pt⟩ := prepareCorrect_of_check ((driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).regG)
      hc.prepOk a w
    exact ⟨fun _ _ _ he => pr _ _ _ (hr _ _ _ he), fun _ he => pt _ (ht _ he)⟩
  have hI := iselSim_relW_cleanup_validated_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot (fun _ => 0) hcs hrel hargs htr
    fuel
  have hRL : ∀ (w₀ : Arm.ArmState) (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64)
      (s : Arm.ArmState), ActEntryR P vcp rf af fa fb K F G X H base ra s w₀ → _ :=
    fun w₀ H G base ra s he => by
      have h := hM6.worldX_value hc.checkAlloc hc.alloc hc.emit hc.layout (X := X) (H := H)
        (K := K) (G := G) (gv := GotV vcp) (P := P) hcov he.abi he.stack he.gfree (by rw [he.hF]; exact he.calls)
        (by rw [he.hF]; exact he.tries) (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body)
        (fun _ => 0)
      rw [he.hF] at h
      exact h
  obtain ⟨us, outs, w, hv, hus, hlen, hhold, hmemR⟩ := hI.1 vals cm hrun
  have hrs : vc.RetsSite us := by
    obtain ⟨b, k, ρ, w₁, vb, ops, outs', -, hvb, hk, -⟩ := hv
    exact retsSite_of_skipStage ⟨b, vb, k, hvb, hk⟩
  refine ⟨us, outs, w, hus, hlen, hhold, hmemR, hrs, fun H G base ra s he => ?_,
    fun hNI hTls D w₀' hrel' hsw hreg hstk H G base ra s he => ?_⟩
  · have hP := hPrep
      (fun _ => 0) w₀
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hRL w₀ H G base ra s he).1 us outs w
      (vReturns_gotV_valueR (hP.1 _ _ _ hv))
    exact ⟨n, ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  · obtain ⟨us', outs', w1, w2, hv1, hv2, hsw12⟩ := vcode_ni_value_validated_stageR (hPg := hPg) (hPi := hPi) hsub hc hX hXI hsym hslot
      hNI hTls
      (fun _ => 0) hcs hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
    obtain ⟨rfl, rfl, rfl⟩ := vRetFrom_det (vs := ⟨0, 0, fun _ => 0, w₀⟩) hv1 hv
    have hP := hPrep
      (fun _ => 0) w₀'
    obtain ⟨n, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ := (hRL w₀' H G base ra s he).1 us' outs' w2
      (vReturns_gotV_valueR (hP.1 _ _ _ hv2))
    refine ⟨n, ⟨h1, h2, fun a ha => ?_, fun g hg h29 h31 => ?_, h5, h6⟩, h7, h8⟩
    · rw [h3 a (fun hf => ha (.inl hf))]
      exact (hsw12.2.1 a ha).symm
    · rw [h4 g hg h29 h31]
      exact (hsw12.1 g hg).symm

end

end E2E

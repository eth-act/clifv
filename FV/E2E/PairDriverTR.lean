import FV.E2E.PairDriverT
import FV.E2E.PairDriverR
import FV.E2E.GuardedFPR
import FV.E2E.LinkWorldTR

/-!
# Non-interference of a typed compiled function at the register-guarded semantics
(#753, stage R2)

`PairDriverT` at `csemR P`, under the typed call families with registers and the contracts with
registers (`RegCompatGot`, `RegCompatInd`):

* `lowerInstOk_pairFR`, `lowerTryOk_pairFR` (`lowerInstOk_pairF`/`lowerTryOk_pairF` for the
  register-guarded `csemGF`);
* `instCalls_pairTR`, `termCalls_pairTR`, `tryCalls_pairTR`, `tryIndCalls_pairTR`, `vcode_niTR`.
-/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The guarded simulation composition of one statement on the register-guarded
semantics, with the float accesses** (`lowerInstOk_pairF` at `csemR P`). -/
theorem lowerInstOk_pairFR {P : BitVec 64 → Clif.Signature → Prop}
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {inst : Clif.Inst} {results : List Nat}
    {st : LState} {rss : List (List Reg)} {st' : LState} {ms : List MInst}
    (hcf : ctx.func = f) (hsig : IndSigOk f (indSigs f) inst)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerInstOkP Rd Pc
        (regG P (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
        (RelW Γ f c) env p ctx inst results st rss st' ms) :
    LowerInstOk (pairSem (csemR P F ctx' X)) (MRP Γ f c D) env p ctx inst results st
      rss st' ms := by
  subst hΓ
  exact lowerInstOk_pair_of
    (semG := fun Rd Pc =>
      regG P (csemGF Γ.F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
    (fun _ _ => regG_mono fun _ _ _ _ h => csemGF_sub h)
    (fun fr cm => lockstep_regG (guardedStepF (D := D) hNI hTls ctx' inst fr cm ms))
    hcf hsig key

/-- **The guarded simulation composition of a `try_call` on the register-guarded
semantics, with the float accesses** (`lowerTryOk_pairF` at `csemR P`). -/
theorem lowerTryOk_pairFR {P : BitVec 64 → Clif.Signature → Prop}
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkP Rd Pc
        (regG P (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOk (pairSem (csemR P F ctx' X)) (MRP Γ f c D) env p ctx ci info st st'
      ms := by
  subst hΓ
  exact lowerTryOk_pair_of
    (semG := fun Rd Pc =>
      regG P (csemGF Γ.F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
    (fun _ _ => regG_mono fun _ _ _ _ h => csemGF_sub h)
    (fun fr cm => lockstep_regG
      (guardedStepF (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)))
    hpin key

/-- **The typed statement calls on pairs of worlds, register-guarded semantics.** -/
theorem instCalls_pairTR (hc : CompiledT f k vc vcp rf af fa fb) (hT : TypedRules)
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
    {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackT_of_check hc.lowerOk)
    (outgoing_le_intBaseAT hc.toA)
  have hIstk := indStack_mono (indStackT_of_check hc.lowerOk)
    (outgoing_le_intBaseAT hc.toA)
  refine lowerInstOk_pairFR hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTermT lowerRulesCorrectTI_program
    lowerRulesCorrectT_program lowerRulesCorrectFT_program nonEUnmatchableT_program
    callRulesCorrectTPR_program indRulesCorrectTPR_program memRulesCorrectRTI_program
    memRulesCorrectRT_program (Refines.regG refines_csemGF)
    (mrStable_relW Γ f c)
    (callsRefinePR_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg)
    (indCallsRefinePR_csemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi)
    (MemRefinesR.regG (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (MemRefinesFP.regG (memRefinesFP_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot))
    hctx hsc (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig hIstk
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **The typed terminator calls on pairs of worlds, register-guarded semantics.** -/
theorem termCalls_pairTR {P : BitVec 64 → Clif.Signature → Prop} {f₀ : Clif.Function}
    (Γ : Rel) (hΓ : Γ.F = F) (hTls : XTls F X)
    (ctx' : FnCtx) (hT : TypedRules) {ctx : Ctx} (hctx : CtxT f₀ ctx) :
    TermCallsT ctx (pairSem (csemR P F ctx' X)) (MRP Γ f₀ c D) := by
  intro ti t data targets out st st' tr hbt hip htl hph hvb hd hemp hrun
  have key : ∀ (Rd : BitVec 64 → Prop), LowerTermOkT
      (regG P (csemG F ctx' X Rd Γ.syms [] [] 0 (fun _ _ _ _ => False)))
      (RelW Γ f₀ c) (termCtx ctx ti data) t targets st st' st'.emitted.toList := fun Rd =>
    termCallsT_of_rules hT.term hT.termUn hT.branch hT.branchEx (Refines.regG refines_csemG)
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
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csemR P Γ.F ctx' X)
         (regG_mono csemG_sub') (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, us1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, h1, h2, h3, hmr1, hmr2, hR⟩)
    | (obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, htc⟩ := r1
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -⟩ := r2
       obtain ⟨w1', w2', he, hp, -, -⟩ := pair_stop (sem := csemR P Γ.F ctx' X)
         (regG_mono csemG_sub') (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, w1'), outs1, (wb, w2'), hp, htc⟩)
    | (refine ⟨r1.1, fun j hj => ?_⟩
       obtain ⟨hU, k1, i1, ops1, ρ1, wa, outs1, wb, hs1, hk, hmr1⟩ := r1.2 j hj
       obtain ⟨-, k2, i2, ops2, ρ2, wa', outs2, wb', hs2, -, hmr2⟩ := r2.2 j hj
       obtain ⟨w1', w2', he, hp, hR1, hR⟩ := pair_stop (sem := csemR P Γ.F ctx' X)
         (regG_mono csemG_sub') (lockstep_regG hstep) (w := q.1) (w' := q.2) hsw hs1 hs2
       injection he with _ _ _ _ hwa _ hwb
       rw [← hwa, ← hwb] at hp
       rw [← hwb] at hR
       exact ⟨hU, k1, i1, ops1, ρ1, (wa, wa'), outs1, (wb, wb'), hp, hk, hmr1, hmr2, hR⟩)

/-- **The typed `try_call` calls on pairs of worlds, register-guarded semantics.** -/
theorem tryCalls_pairTR (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryCallsT f ctx (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
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
  refine lowerTryOk_pairFR hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.inv.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkPR_runTermT tryRulesCorrectTPR_program hT.tryUn
    (Refines.regG refines_csemGF)
    (mrStable_relW Γ f c)
    (MemRefinesR.regG (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (outArgsOk_relW Γ f c)
    (callsRefinePR_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg) hctx'
    (externsIn_self f) hra hd hip' he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
    (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok

/-- **The typed `try_call_indirect` calls on pairs of worlds, register-guarded
semantics.** -/
theorem tryIndCalls_pairTR (hIstk : IndStack (indSigs f) (RAFrame.compute vcp rf).intBase)
    (hT : TypedRules)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPi : RegCompatInd P env (indSigs f) syms)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryIndCallsT f ctx (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
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
  have hsd := Backend.exnTableOpnd_sig he
  refine lowerTryOk_pairFR hNI hTls (Γ := Γ) rfl (fun fr cm hfr => ?_) fun Rd Pc => ?_
  · have hfg : fr.func = f := hfr.trans hctx'.inv.func
    refine ⟨(fun _ _ _ _ _ _ _ h => by cases h), fun sg cl ar s x vals n gg rvals cm' hi' hs hc' hv
      hsy hg hgo hty => ?_⟩
    cases hi'
    rw [hfg, hsd] at hs
    cases hs
    exact ⟨rfl, ⟨.inr ⟨hsig, hty⟩, gg, rvals, cm', hg, hgo⟩, .inr ⟨_, _, _, rfl, hfg ▸ hsd, hv⟩⟩
  · obtain ⟨ms, hem, hok⟩ := tryIndOkPR_runTermT tryIndRulesCorrectTPR_program hT.tryIndUn
      (Refines.regG refines_csemGF)
      (mrStable_relW Γ f c)
      (MemRefinesR.regG (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) rfl hsym))
      (outArgsOk_relW Γ f c)
      hIstk
      (indCallsRefinePR_csemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi)
      hctx' hd hip' he hsig hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
      (Nat.le_refl _) hrun
    have : ms = st'.emitted.toList := by
      simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
    rw [← this]
    exact hok

/-- **Non-interference of a typed compiled function's VCode run at the register-guarded semantics**
(`vcode_niT` at `csemR P`). -/
theorem vcode_niTR (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
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
      ∃ us outs w w', VReturns vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀ us outs w ∧
        VReturns vc (csemR P F ⟨fa.k, af.slotBase⟩ X) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligationsT_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have H := driverHypT_relWR (hPg := hPg) (hPi := hPi) (c := c) hsub hc hT hX hXI hsym
    hslot hshape hcert hbr
  have hctxT : CtxT f ctx :=
    ctxT_of_functionET hsub.subsetET hshape.hctx.choose_spec hshape.ctxInvT hshape.scope
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hmem : MemRefines F slotOff syms (csemR P F ⟨fa.k, af.slotBase⟩ X) :=
    (memRefines_csem _ _ X hslot hsym).regG
  have houtB := outgoing_le_intBaseAT hc.toA
  have HP : DriverHypT f vc ctx st0 R gn bl A (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
      (MRP Γ f c D) env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pairR P F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pairTR (hPg := hPg) (hPi := hPi) hc hT hX hXI hsym hslot hNI hTls
      hctxT hshape.scope hstT
    terms := termCalls_pairTR (P := P) Γ rfl hTls ⟨fa.k, af.slotBase⟩ hT hctxT
    ext := H.ext
    indSig := H.indSig
    subET := H.subET
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pairTR (hPg := hPg) hT hX hsym hslot hNI hTls hctxT,
      tryStack_mono (tryStackT_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pairTR
      (indStack_mono (indStackT_of_check hc.lowerOk) (outgoing_le_intBaseAT hc.toA))
      hT hXI (hPi := hPi) hsym hNI hTls hctxT
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP := runPrem_of_traps hce htr
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2T H
    (driverSem_csemR P F ⟨fa.k, af.slotBase⟩ X) hmem
    (memRefinesFP_csem (fun _ => True) F _ X hslot).regG (mrStable_relW Γ f c) hB0 hce.callers
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

end

end E2E

import FV.E2E.PairDriverTC
import FV.E2E.PairDriverTR
import FV.E2E.LinkWorldTCR
import FV.E2E.TypedRulesSR
import FV.Backend.Proof.LowerContractTCR
import FV.Backend.Proof.LowerContractTFSOR

/-!
# Non-interference of a compiled function with typed `try_call`s and the proven float operations,
at the register-guarded semantics (#753, stage R2)

`PairDriverTC` at `csemR P`, under the typed call families with registers and the contracts with
registers (`RegCompatGot`, `RegCompatInd`):

* `tryOkPCR_of_rules`, `tryOkPCR_runTerm` (`tryOkPC_of_rules`/`tryOkPC_runTerm` from the typed
  `try_call` family with registers `tryRulesCorrectTFPR_program`);
* `lowerTryOkC_pairFR`, `instCalls_pairTCFSOR`, `tryCalls_pairTCR` and its `CtxTW`/`CtxTS S`
  forms `tryCalls_pairTCWR`/`tryCalls_pairTCSR`, `termCalls_pairTWR`/`termCalls_pairTSR`,
  `tryIndCalls_pairTWR`/`tryIndCalls_pairTSR` (transported, `ctxWR_transport`,
  `scopeSR_transport`);
* `vcode_niTCFR`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- `tryOkPC_of_rules` under the call contract with registers (`CallsRefinePR`, from the proven
typed `try_call` family with registers `tryRulesCorrectTFPR_program`). -/
theorem tryOkPCR_of_rules {p : Program} (hp : Data p) (hrules : TryRulesCorrectTFPR p)
    (hun : TryUnmatchableTC p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hcr : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
  change 1002 + (p.rulesOf 687).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t687 term_687_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower_branch := by
    change r ∈ p.rulesOf 687; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧ ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run
        (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_branch_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : tryRootRule r
  · exact absurd hmatch (hun r hr hroot ctx f ti fn args et data targets hd hi cfg m (st, tr) env' s1)
  · obtain ⟨ms, h1, h2⟩ := hrules Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout
      hcr r hr hroot f ctx hctx hext ti fn args et data sig items targets info lo st1 hra hd he hi
      hinfo htr hvb cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch
      heval
    exact ⟨ms, h1, h2⟩

set_option maxRecDepth 20000 in
/-- `tryOkPCR_of_rules` for the exported program and the backend's call on a typed `try_call`. -/
theorem tryOkPCR_runTerm
    {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem)
    (hFP : MemRefinesFP Rd F sb isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hcr : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hctx : CallCtxT f ctx) (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower_branch).length ≤ 1000 := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]; decide
    obtain ⟨ms, h1, h2⟩ := tryOkPCR_of_rules data_program tryRulesCorrectTFPR_program
      tryUnmatchableTC_program hR hMR hMem hFP hout hcr hctx hext hra hd he hi hinfo htr hvb rfl
      (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin} {X : ExtSem} {syms : String → Option Nat}
  {slotOff : Nat} {env : Clif.Env} {F : BitVec 64 → Prop} {c : BitVec 64} {D : BitVec 64 → Prop}

/-- **The guarded simulation composition of a typed `try_call` on the register-guarded semantics,
with the float accesses** (`lowerTryOkC_pairF` at `csemR P`). -/
theorem lowerTryOkC_pairFR {P : BitVec 64 → Clif.Signature → Prop}
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {Γ : Rel} (hΓ : Γ.F = F) {ctx' : FnCtx} {ctx : Ctx} {ci : Clif.Inst} {info : TryInfo}
    {st st' : LState} {ms : List MInst}
    (hpin : ∀ (fr : Clif.Frame) (cm : Clif.Mem), fr.func = ctx.func →
      CallPin (StepPin env (f.externs.map (·.2)) (indSigs f) ci fr cm) env ci fr cm)
    (key : ∀ (Rd : BitVec 64 → Prop)
      (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop),
      LowerTryOkPC Rd Pc
        (regG P (csemGF F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
        (RelW Γ f c) env p ctx ci info st st' ms) :
    LowerTryOkC (pairSem (csemR P F ctx' X)) (MRP Γ f c D) env p ctx ci info st st' ms := by
  subst hΓ
  exact lowerTryOkC_pair_of
    (semG := fun Rd Pc =>
      regG P (csemGF Γ.F ctx' X Rd syms (f.externs.map (·.2)) (indSigs f) c Pc))
    (fun _ _ => regG_mono fun _ _ _ _ h => csemGF_sub h)
    (fun fr cm => lockstep_regG (guardedStepF (D := D) hNI hTls ctx' ci fr cm (tryFix info ms)))
    hpin key

/-- **`instCalls_pairTCFS` over a scope inside `InstScopeTFLO`** (#35: `fcopysign` and `fma` among
the instructions; `lowerInstOkPR_runTermTFSO` with `lowerRulesCorrectCS_program`,
`lowerRulesCorrectFM_program` and the context's `FmaNegYFree`). -/
theorem instCalls_pairTCFSOR {S : InstScope} (hS : ∀ ctx, S.P ctx → InstScopeTFLO ctx)
    (hc : CompiledTCF f k vc vcp rf af fa fb) (hT : TypedRulesS S)
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
    InstCallsT f ctx (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
      (MRP ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c D) env p := by
  intro ii info inst st rss st' tr hmem hi hcl hsig hemp hvb hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hstk := callsStack_mono (callsStackTCF_of_check hc.lowerOk)
    (outgoing_le_intBaseATCF hc.toA)
  refine lowerInstOk_pairFR hNI hTls (Γ := Γ) rfl hctx.inv.func hsig fun Rd Pc => ?_
  obtain ⟨B, hB, stm, hstm, hst'⟩ := hmem
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOkPR_runTermTFSO hS (lowerRulesCorrectTIS_program S)
    lowerRulesCorrectT_program lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program
    lowerRulesCorrectFC_program lowerRulesCorrectCS_program lowerRulesCorrectFM_program
    (nonEUnmatchableTFSO_program hS) callRulesCorrectTFPR_program
    (indRulesCorrectTPRS_program S) (memRulesCorrectRTIS_program S) memRulesCorrectRT_program (Refines.regG refines_csemGF)
    (mrStable_relW Γ f c)
    (callsRefinePR_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg)
    (indCallsRefinePR_csemGF hXI hsym (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPi)
    (MemRefinesR.regG (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (MemRefinesFP.regG (memRefinesFP_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)) (PoolRefinesFP.regG poolRefinesFP_csemGF)
    hctx hfn (outArgsOk_relW Γ f c) (externsIn_self f) (memRelOk_relW Γ f c) hi hcl hsig
    (indStack_mono (indStackTCF_of_check hc.lowerOk) (outgoing_le_intBaseATCF hc.toA))
    (hst ii info inst hi hcl)
    (fun fn args e hc' he => hstk B hB stm hstm fn args e (hst' ▸ hc') he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

/-- **The typed `try_call` calls on pairs of worlds** (`TryCallsTC` of `pairSem`): the typed
rule contracts with pinned calls at the guarded semantics with the float accesses `csemGF`,
paired (`lowerTryOkC_pairF`). -/
theorem tryCalls_pairTCR (hT : TypedRules)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    {P : BitVec 64 → Clif.Signature → Prop}
    (hPg : RegCompatGot P (f.externs.map (·.2)) (fun n => X.sym n 0))
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    {ctx : Ctx} (hctx : CtxT f ctx) :
    TryCallsTC f ctx (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X))
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
  refine lowerTryOkC_pairFR hNI hTls (Γ := Γ) rfl
    (fun fr cm hfr => callPin_stepPin (env := env) (cm := cm) (inst := .call fn args)
      (hfr.trans hctx'.func) (fun _ _ _ _ h => by cases h)) fun Rd Pc => ?_
  obtain ⟨ms, hem, hok⟩ := tryOkPCR_runTerm (isem := regG P (csemGF F ⟨fa.k, af.slotBase⟩ X Rd Γ.syms
    (f.externs.map (·.2)) (indSigs f) c Pc)) (Refines.regG refines_csemGF) (mrStable_relW Γ f c)
    (MemRefinesR.regG (memRefinesR_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot hsym))
    (MemRefinesFP.regG (memRefinesFP_csemGF (ctx := ⟨fa.k, af.slotBase⟩) hslot)) (outArgsOk_relW Γ f c)
    (callsRefinePR_csemGF hX (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.2.1) hPg) hctx'
    (externsIn_self f) hra hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] })
    (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]
  exact hok

-- **`tryCalls_pairTCR` over `CtxTW` and over `CtxTS S`.**
ctxWR_transport tryCalls_pairTCR => tryCalls_pairTCWR
scopeSR_transport tryCalls_pairTCWR => tryCalls_pairTCSR

-- **`termCalls_pairTR` and `tryIndCalls_pairTR` over `CtxTW` and over `CtxTS S`.**
ctxWR_transport termCalls_pairTR => termCalls_pairTWR
ctxWR_transport tryIndCalls_pairTR => tryIndCalls_pairTWR
scopeSR_transport termCalls_pairTWR => termCalls_pairTSR
scopeSR_transport tryIndCalls_pairTWR => tryIndCalls_pairTSR

/-- **Non-interference of a compiled function's VCode run, with the proven float operations**
(`vcode_ni` for the scope with the proven float operations): two body-entry worlds related to
the same CLIF entry, that agree outside `F ∪ D`, with the same argument registers and
stack-passed argument bytes, return (for a returning CLIF run) through the same `rets` with the
same values, final worlds that agree outside `F ∪ D`. -/
theorem vcode_niTCFR (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
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
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hS : ∀ ctx, InstScope.tflo.P ctx → InstScopeTFLO ctx := fun _ h => h
  have H := driverHypTCFSO_relWR (S := InstScope.tflo) (hPg := hPg) (hPi := hPi) hS (c := c) hsub hc hX hXI hsym hslot
    hshape hcert hbr
  have hctxT : CtxTS InstScope.tflo f ctx := ⟨hshape.ctxInvT, hshape.scope⟩
  have hstT : StoresTyped ctx := storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  have hfn : FmaNegYFree ctx := fmaNegYFree_of_buildCtx (Compile.fmaNegYFree_of_functionETCF
    hsub.subsetETCF) hshape.hctx.choose_spec hshape.ctxInvT
  have hmem : MemRefines F slotOff syms (csemR P F ⟨fa.k, af.slotBase⟩ X) :=
    (memRefines_csem _ _ X hslot hsym).regG
  have houtB := outgoing_le_intBaseATCF hc.toA
  have hTS := typedRulesS_program InstScope.tflo
  have HP : DriverHypTCS InstScope.tflo f vc ctx st0 R gn bl A
      (pairSem (csemR P F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D) env p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pairR P F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pairTCFSOR (hPg := hPg) (hPi := hPi) hS hc hTS hX hXI hsym hslot hNI hTls hctxT hfn hstT
    terms := termCalls_pairTSR _ (P := P) Γ rfl hTls ⟨fa.k, af.slotBase⟩ hTS hctxT
    ext := H.ext
    indSig := H.indSig
    subETC := H.subETC
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pairTCSR _ hTS hX (hPg := hPg) hsym hslot hNI hTls hctxT,
      tryStack_mono (tryStackTCF_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pairTSR _
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
  have hR := sim_runTCS _ HP hP fuel cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ (.refl _) hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -, -⟩ := hR
  obtain ⟨h1, h2⟩ := vRetFrom_pair hret
  exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1 h1, VRetFrom.prefix hs2 h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

end

end E2E

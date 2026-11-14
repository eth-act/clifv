import FV.Backend.Proof.LowerContractTPF
import FV.Backend.Proof.IselCtlCallF

/-!
# The typed statement dispatcher with float calls (S11g, #1015)

`LowerContractTF.lean`'s / `LowerContractTPF.lean`'s statement dispatchers over contexts whose
`call` statements may take and return `f32`/`f64` (`CtxTW`: no condition on the callees of the
`call`s and on the classes of their arguments; the scope `Compile.functionETCF` gives it,
`ctxT_of_functionETCF`). The first matching root of `lower` is

* a non-closure root: never matches (`lower_nonroot_nomatchTFC`: the exclusion checker over
  `floatOpsFC`, in which a `call` of a callee returning a float has a float result);
* a float root (movement, memory, arithmetic, conversion, `fcmp`) or the float arm of `select`;
* on a subset-E instruction other than a `call`, an integer root;
* on a `call`, a `call` root (rules 1031 `bl`, 1032 GOT + `blr`): the float family
  `CallRulesCorrectTFP` (`IselCtlCallF`; arguments in their values' classes, x0..x7 / v0..v7,
  then the stack, `str s`/`str d` for a float under `MemRefinesFP`; returns from `retRegsC`'s
  registers), whose contexts are `CallCtxT` (`CtxInvT.toCallCtx`) — every `call`, integer or
  not, goes through it, so `CallRulesCorrectT` is not needed;
* on another instruction of the scope, no other closure root (`NonEUnmatchableTFW`).

Generated code is unchanged: these are the proofs of the shipped lowering.

* `lowerInstOkP_of_rulesTFW`, `lowerInstOkP_runTermTFW` (pinned obligations, `LowerInstOkP`);
* `lowerInstOk_of_rulesTFW`, `lowerInstOk_runTermTFW`, `instCallsTFW_of_rules` (unpinned, from
  the pinned ones at `Rd = Pc = True`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

set_option maxRecDepth 20000 in
/-- **The typed statement dispatcher with pinned obligations, the proven float operations and
float calls** (`lowerInstOkP_of_rulesTF` over `CtxTW`: the exclusion `lower_nonroot_nomatchTFC`,
the non-E unmatchability `NonEUnmatchableTFW`, every `call` by `CallRulesCorrectTFP`). -/
theorem lowerInstOkP_of_rulesTFW (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hCvt : LowerRulesCorrectCvtT program) (hFC : LowerRulesCorrectFC program)
    (hnE : NonEUnmatchableTFW program) (hcalls : CallRulesCorrectTFP program)
    (hind : IndRulesCorrectTP program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxTW f ctx) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hIstk : IndStack sigs outB) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (program.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
  have hp := data_program
  change 1002 + (program.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ program.rulesOf TId.lower := by
    change r ∈ program.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, program.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre,
      ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule program (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  have hm1 : 1000 ≤ m := by omega
  have hn1 : 1000 ≤ n := by omega
  have hmF : floatMemRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfmem
    obtain ⟨ms, rss, h1, h2, h3⟩ := hmemF Rd F sb syms isem MR env cp hR hMR hMem hFP r hr hfmem
      f ctx hctx.inv hMRo ii info inst hi hc cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb
      hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  have hmv : floatMoveRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfm
    obtain ⟨ms, rss, h1, h2, h3⟩ := (hT F isem MR env cp hR hMR).1 r hr hfm f ctx hctx.inv ii info
      inst hi hc (f64PoolFreeInst_of_instETF (hctx.scope ii info inst hi hc)) cfg hco m n st tr
      env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  have har : floatArithRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfa
    obtain ⟨ms, rss, h1, h2, h3⟩ := hFT F isem MR env cp hR hMR r hr hfa f ctx hctx.inv ii info
      inst hi hc trivial cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  have hcv : floatCvtRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfc
    obtain ⟨ms, rss, h1, h2, h3⟩ := hCvt F isem MR env cp hR hMR r hr hfc f ctx hctx.inv ii info
      inst hi hc trivial cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  have hfc' : floatCmpRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfcmp
    obtain ⟨ms, rss, h1, h2, h3⟩ := hFC F isem MR env cp hR hMR r hr hfcmp f ctx hctx.inv ii info
      inst hi hc trivial cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  cases hroot : closureRoot r
  · exact absurd hmatch (lower_nonroot_nomatchTFC hctx.inv hctx.scope hi hc hr
      (by rw [← closureRoot_eq]; exact hroot) cfg m (st, tr) env' s1)
  cases hE : Compile.instE inst
  · -- an instruction of the scope outside subset E
    cases hfm : floatMoveRootRule r
    · cases hfmem : floatMemRootRule r
      · cases hfa : floatArithRootRule r
        · cases hfc : floatCvtRootRule r
          · cases hfcmp : floatCmpRootRule r
            · by_cases hsel : r.id = 971 ∧ FloatSelect inst
              · obtain ⟨ms, rss, h1, h2, h3⟩ := (hT F isem MR env cp hR hMR).2 r hr hsel.1 f ctx
                  hctx.inv ii info inst hi hc hsel.2 cfg hco m n st tr env' s1 out st' tr2 hm1 hn1
                  hvb hfirst hmatch heval
                exact ⟨ms, rss, h1, h2, h3.toP⟩
              · exact absurd hmatch (hnE r hr hroot hfm hfmem hfa hfc hfcmp f ctx hctx ii info inst
                  hi hc hE (fun h1 h2 => hsel ⟨h1, h2⟩) hst cfg m st tr env' s1 hfirst)
            · exact hfc' hfcmp
          · exact hcv hfc
        · exact har hfa
      · exact hmF hfmem
    · exact hmv hfm
  · -- a subset-E instruction
    cases hcall : callRootRule r
    · cases hind' : indRootRule r
      · cases hm : memRootRule r
        · cases hfm : floatMoveRootRule r
          · cases hfa : floatArithRootRule r
            · obtain ⟨ms, rss, h1, h2, h3⟩ := hrules F isem MR env cp hR hMR r hr hroot hcall hind'
                hm hfm hfa f ctx hctx ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr2
                hm1 hn1 hvb hfirst hmatch heval
              exact ⟨ms, rss, h1, h2, h3.toP⟩
            · exact har hfa
          · exact hmv hfm
        · cases hfmem : floatMemRootRule r
          · obtain ⟨ms, rss, h1, h2, h3⟩ := hmem Rd F sb syms isem MR env cp hR hMR hMem r hr hm
              hfmem f ctx hctx hMRo ii info inst hi hc hE cfg hco m n st tr env' s1 out st' tr2 hm1
              hn1 hvb hfirst hmatch heval
            exact ⟨ms, rss, h1, h2, h3.toP⟩
          · exact hmF hfmem
      · exact hind Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hicr r hr hind'
          f ctx hctx ii info inst hi hc
          hE hsig cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    · -- a `call` root: the float family, for every extern signature
      exact hcalls Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hFP hout hcr r hr hcall f ctx
        hctx.inv.toCallCtx hnorm ii info inst hi hc hstk cfg hco m n st tr env' s1 out st' tr2 hm1
        hn1 hvb hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOkP_of_rulesTFW` for the backend's own call (`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOkP_runTermTFW (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hCvt : LowerRulesCorrectCvtT program) (hFC : LowerRulesCorrectFC program)
    (hnE : NonEUnmatchableTFW program) (hcalls : CallRulesCorrectTFP program)
    (hind : IndRulesCorrectTP program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxTW f ctx) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hIstk : IndStack sigs outB) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
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
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOkP_of_rulesTFW hrules hT hFT hCvt hFC hnE hcalls
      hind hmem hmemF hR hMR hcr hicr hMem hFP hctx hout hnorm hMRo hi hc hsig hIstk hst hstk rfl
      (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

/-- **The typed statement dispatcher with float calls, unpinned** (`lowerInstOkP_runTermTFW` at
`Rd = Pc = True`). -/
theorem lowerInstOk_runTermTFW (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hCvt : LowerRulesCorrectCvtT program) (hFC : LowerRulesCorrectFC program)
    (hnE : NonEUnmatchableTFW program) (hcalls : CallRulesCorrectTFP program)
    (hind : IndRulesCorrectTP program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefine F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefine env sigs MR isem)
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxTW f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hIstk : IndStack sigs outB) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
  obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOkP_runTermTFW (Rd := fun _ => True)
    (Pc := fun _ _ _ _ => True) hrules hT hFT hCvt hFC hnE hcalls hind hmem hmemF hR hMR
    (hcr.toP _) (hicr.toP _) (memRefinesR_of hMem) hFP hctx hout hnorm hMRo hi hc hsig hIstk hst
    hstk hvb h
  exact ⟨ms, rss, h1, h2, h3.toOk⟩

/-- **From the typed rule families with float calls to the driver's `lower` calls**
(`instCallsTF_of_rules` over `CtxTW`, every `call` by `CallRulesCorrectTFP`). -/
theorem instCallsTFW_of_rules (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hT : LowerRulesCorrectT Isle.Aarch64.program) (hFT : LowerRulesCorrectFT Isle.Aarch64.program)
    (hCvt : LowerRulesCorrectCvtT Isle.Aarch64.program)
    (hFC : LowerRulesCorrectFC Isle.Aarch64.program)
    (hnE : NonEUnmatchableTFW Isle.Aarch64.program)
    (hcalls : CallRulesCorrectTFP Isle.Aarch64.program)
    (hind : IndRulesCorrectTP Isle.Aarch64.program) (hmem : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefine env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hstk : CallsStack f outB) (hIstk : IndStack (indSigs f) outB)
    (hMRo : MemRelOk F sb syms f MR) (hctx : CtxTW f ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx sem MR env p := by
  intro ii info inst st rss st' tr hmem' hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOk_runTermTFW hrules hT hFT hCvt hFC hnE hcalls hind
    hmem hmemF (env := env) (cp := p) hR hMR hcr hicr hMem hFP hctx hout (externsIn_self f) hMRo hi
    hc hsig hIstk (hst ii info _ hi hc)
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

end Backend.Proof

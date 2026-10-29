import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.IselExclTF

/-!
# The typed statement dispatcher with the proven float operations (S11f, #35)

`LowerContractT.lean`'s statement dispatcher for contexts whose instructions may also be the
S11f float arithmetic, rounding, conversions and scalar comparisons (`CtxT`, whose scope is
`InstScopeTF`): the first matching root of `lower` is a non-closure root (never matches,
`lower_nonroot_nomatchTF_calls`), a float-movement, float-memory, float-arithmetic
(`LowerRulesCorrectFT`), conversion (`LowerRulesCorrectCvtT`) or `fcmp` root
(`LowerRulesCorrectFC`, `IselFloatCmp`), the float arm of `select`, or on a subset-E instruction
an integer root; on another instruction no other closure root matches (`NonEUnmatchableTF`).

* `floatCvtRootRule` (the sixteen S11f-cvt roots of `lower`, `lower.isle:724-794`),
  `LowerRulesCorrectCvtT` (they are correct over float-capable contexts);
* `NonEUnmatchableTF`: `NonEUnmatchableT` over `InstScopeTF` with the conversion and `fcmp`
  roots among the float roots;
* `lowerInstOk_of_rulesTF`, `lowerInstOk_runTermTF`, `instCallsTF_of_rules`.

`lowerInstOk_of_rulesT`, `lowerInstOk_runTermT`, `instCallsT_of_rules` and `NonEUnmatchableT`
are unchanged (they take `InstScopeT` explicitly).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

/-- The float ↔ integer conversion roots of `lower` (S11f-cvt, `closure.rs`
`BACKEND_FLOAT_ROOTS`): `fcvt_from_uint` (723-726: `rule_lower_724/727/730/733`),
`fcvt_from_sint` (729-732: `rule_lower_744/747/750/753`), `fcvt_to_uint_sat` (735-738:
`rule_lower_764/767/770/773`), `fcvt_to_sint_sat` (741-744: `rule_lower_784/787/790/793`). -/
def floatCvtRootRule (r : Rule) : Bool :=
  r.id == 723 || r.id == 724 || r.id == 725 || r.id == 726 || r.id == 729 || r.id == 730 ||
    r.id == 731 || r.id == 732 || r.id == 735 || r.id == 736 || r.id == 737 || r.id == 738 ||
    r.id == 741 || r.id == 742 || r.id == 743 || r.id == 744

/-- **S11f-cvt's target**: over float-capable contexts, the conversion roots are correct (CLIF's
`fcvt_*` and the emitted `ucvtf`/`scvtf`/`fcvtzu`/`fcvtzs` compute the same function). -/
def LowerRulesCorrectCvtT (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, floatCvtRootRule r = true → LowerRuleOkT isem MR env cp p r

/-- **The closure roots of `lower` other than the float ones never match a non-E instruction
of a typed context with the proven float operations** (`NonEUnmatchableT` over `CtxT`'s scope
`InstScopeTF`, the conversion and `fcmp` roots among the float roots): on an instruction of the
scope outside subset E (the float movement, arithmetic, rounding, conversions, comparisons), the
first matching closure root is a float-movement, float-memory, float-arithmetic, conversion or
`fcmp` root, or the `select` root 971 on a float `select`. -/
def NonEUnmatchableTF (p : Program) : Prop :=
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → floatMoveRootRule r = false →
    floatMemRootRule r = false → floatArithRootRule r = false → floatCvtRootRule r = false →
    floatCmpRootRule r = false →
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instE inst = false → (r.id = 971 → ¬ FloatSelect inst) →
    StoreTyped ctx inst →
  ∀ (cfg : Config) (m : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V)
    (s1 : LState × Array RuleId),
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) ≠ .ok (some env', s1)

set_option maxRecDepth 20000 in
/-- **The typed statement dispatcher with the proven float operations**
(`lowerInstOk_of_rulesT` over `CtxT` alone, with the conversion and `fcmp` roots and
`NonEUnmatchableTF`). -/
theorem lowerInstOk_of_rulesTF (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hCvt : LowerRulesCorrectCvtT program) (hFC : LowerRulesCorrectFC program)
    (hnE : NonEUnmatchableTF program) (hcalls : CallRulesCorrectT program)
    (hind : IndRulesCorrectT program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefine F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefine env sigs MR isem)
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (program.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
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
  -- the float memory roots, under `MemRefinesR True` and `MemRefinesFP True`
  have hmF : floatMemRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfmem
    obtain ⟨ms, rss, h1, h2, h3⟩ := hmemF (fun _ => True) F sb syms isem MR env cp hR hMR
      (memRefinesR_of hMem) hFP r hr hfmem f ctx hctx.inv hMRo ii info inst hi hc cfg hco m n st tr
      env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toOk⟩
  have hmv : floatMoveRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfm => (hT F isem MR env cp hR hMR).1 r hr hfm f ctx hctx.inv ii info inst hi hc
      (f64PoolFreeInst_of_instETF (hctx.scope ii info inst hi hc))
      cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  have har : floatArithRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfa => hFT F isem MR env cp hR hMR r hr hfa f ctx hctx.inv ii info inst hi hc trivial
      cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  have hcv : floatCvtRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfc => hCvt F isem MR env cp hR hMR r hr hfc f ctx hctx.inv ii info inst hi hc trivial
    cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  have hfc' : floatCmpRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOk isem MR env cp ctx inst info.results st rss st' ms :=
    fun hfcmp => hFC F isem MR env cp hR hMR r hr hfcmp f ctx hctx.inv ii info inst hi hc trivial
      cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
  cases hroot : closureRoot r
  · exact absurd hmatch (lower_nonroot_nomatchTF_calls hctx.inv hctx.scope hctx.calls hi hc hr
      (by rw [← closureRoot_eq]; exact hroot) cfg m (st, tr) env' s1)
  cases hE : Compile.instE inst
  · -- an instruction of the scope outside subset E
    cases hfm : floatMoveRootRule r
    · cases hfmem : floatMemRootRule r
      · cases hfa : floatArithRootRule r
        · cases hfc : floatCvtRootRule r
          · cases hfcmp : floatCmpRootRule r
            · by_cases hsel : r.id = 971 ∧ FloatSelect inst
              · exact (hT F isem MR env cp hR hMR).2 r hr hsel.1 f ctx hctx.inv ii info inst hi hc
                  hsel.2 cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
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
            · exact hrules F isem MR env cp hR hMR r hr hroot hcall hind' hm hfm hfa f ctx hctx ii
                info inst hi hc hE cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch
                heval
            · exact har hfa
          · exact hmv hfm
        · cases hfmem : floatMemRootRule r
          · obtain ⟨ms, rss, h1, h2, h3⟩ := hmem (fun _ => True) F sb syms isem MR env cp hR hMR
              (memRefinesR_of hMem) r hr hm hfmem f ctx hctx hMRo ii info inst hi hc hE cfg hco m n
              st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
            exact ⟨ms, rss, h1, h2, h3.toOk⟩
          · exact hmF hfmem
      · exact hind F isem MR env cp sigs hR hMR hicr r hr hind' f ctx hctx ii info inst hi hc hE hsig
          cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    · exact hcalls F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hcall f ctx hctx
        hnorm ii info inst hi hc hE hstk cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst
        hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOk_of_rulesTF` for the backend's own call (`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOk_runTermTF (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hCvt : LowerRulesCorrectCvtT program) (hFC : LowerRulesCorrectFC program)
    (hnE : NonEUnmatchableTF program) (hcalls : CallRulesCorrectT program)
    (hind : IndRulesCorrectT program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefine F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefine env sigs MR isem)
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hst : StoreTyped ctx inst)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOk isem MR env cp ctx inst info.results st rss st' ms := by
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
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOk_of_rulesTF hrules hT hFT hCvt hFC hnE hcalls hind
      hmem hmemF hR hMR hcr hicr hMem hFP hctx hout hnorm hMRo hi hc hsig hst hstk rfl (by omega)
      hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

/-- **From the typed rule families with the proven float operations to the driver's `lower`
calls** (`instCallsT_of_rules` over `CtxT` alone). -/
theorem instCallsTF_of_rules (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hT : LowerRulesCorrectT Isle.Aarch64.program) (hFT : LowerRulesCorrectFT Isle.Aarch64.program)
    (hCvt : LowerRulesCorrectCvtT Isle.Aarch64.program)
    (hFC : LowerRulesCorrectFC Isle.Aarch64.program)
    (hnE : NonEUnmatchableTF Isle.Aarch64.program) (hcalls : CallRulesCorrectT Isle.Aarch64.program)
    (hind : IndRulesCorrectT Isle.Aarch64.program) (hmem : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem) (hMR : MRStable F MR) (hcr : CallsRefine F env (f.externs.map (·.2)) MR sem)
    (hicr : IndCallsRefine env (indSigs f) MR sem)
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hstk : CallsStack f outB)
    (hMRo : MemRelOk F sb syms f MR) (hctx : CtxT f ctx) (hst : StoresTyped ctx) :
    InstCallsT f ctx sem MR env p := by
  intro ii info inst st rss st' tr hmem' hi hc hsig hemp hvb hrun
  obtain ⟨B, hB, stm, hstm, rfl⟩ := hmem'
  obtain ⟨ms, rss', hem, hov, hok⟩ := lowerInstOk_runTermTF hrules hT hFT hCvt hFC hnE hcalls hind
    hmem hmemF (env := env) (cp := p) hR hMR hcr hicr hMem hFP hctx hout (externsIn_self f) hMRo hi
    hc hsig (hst ii info _ hi hc)
    (fun fn args e hc he => hstk B hB stm hstm fn args e hc he) hvb hrun
  cases hov
  rw [hemp, Array.empty_append] at hem
  rw [hem, List.toList_toArray]
  exact hok

end Backend.Proof

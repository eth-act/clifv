import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.IselContractP

/-!
# The typed lowering contracts with pinned calls (S11e5 Stage C, slice 7)

`IselContractP.lean` over typed contexts: the call, `call_indirect`, `try_call` and
`try_call_indirect` families whose run assumes a read guard `Rd` (`InitIn Rd cm`, guarded memory
forms `MemRefinesR Rd`, `MemRefinesFP Rd`) and the pinned CLIF call (`CallPin Pc`), concluding
`LowerInstOkP`/`LowerTryOkP`. The non-interference driver instantiates them per CLIF step at the
guarded semantics `csemGF` on each of two worlds (`E2E/PairDriverT.lean`).

* `CallRulesCorrectTP`, `IndRulesCorrectTP`, `TryRulesCorrectTP`, `TryIndRulesCorrectTP`
  (`CallRulesCorrectP` … with `CtxT`, subset-E statements, `TermIntPos` for `try_call`s), and
  the unpinned families from them: `callRulesCorrectT_of_P`, `indRulesCorrectT_of_P`,
  `tryRulesCorrectT_of_P`, `tryIndRulesCorrectT_of_P`.
* Dispatchers: `lowerInstOkP_of_rulesT`/`lowerInstOkP_runTermT` (the typed statement dispatcher
  `lowerInstOk_of_rulesT` with pinned obligations), `tryOkP_runTermT`, `tryIndOkP_runTermT`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

/-! ## The families -/

/-- `CallRuleOkT` with the pinned obligation. -/
def CallRuleOkTP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → ExternsIn f exts →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  Compile.instE inst = true →
  (∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB) →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms

/-- **The call roots over typed contexts, with pinned calls** (`CallRulesCorrectP` with
`CtxT`). -/
def CallRulesCorrectTP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower, callRootRule r = true →
      CallRuleOkTP Rd Pc isem MR env cp exts outB p r

theorem callRulesCorrectT_of_P {p : Program} (h : CallRulesCorrectTP p) : CallRulesCorrectT p := by
  intro F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot f ctx hctx hexts ii info
    inst hi hc hE hstk cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  obtain ⟨ms, rss, h1, h2, h3⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb
    syms outB hR hMR (memRefinesR_of hMem) hout (hCR.toP _) r hr hroot f ctx hctx hexts ii info
    inst hi hc hE hstk cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  exact ⟨ms, rss, h1, h2, h3.toOk⟩

/-- `IndRuleOkT` with the pinned obligation. -/
def IndRuleOkTP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (sigs : List Clif.Signature) (p : Program) (r : Rule) :
    Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info → info.clif = some inst →
  Compile.instE inst = true → IndSigOk f sigs inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms

/-- **The `call_indirect` root over typed contexts, with pinned calls**, under guarded memory
forms and an outgoing area that holds the stack arguments of every signature of `sigs` (S5). -/
def IndRulesCorrectTP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefineP Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower, indRootRule r = true → IndRuleOkTP Rd Pc isem MR env cp sigs p r

theorem indRulesCorrectT_of_P {p : Program} (h : IndRulesCorrectTP p) : IndRulesCorrectT p := by
  intro F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR r hr hroot f ctx hctx ii
    info inst hi hc hE hsig cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  obtain ⟨ms, rss, h1, h2, h3⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp sigs sb
    syms outB hR hMR (memRefinesR_of hMem) hout hIstk (hCR.toP _) r hr hroot f ctx hctx ii info
    inst hi hc hE hsig cfg hco m n st tr env' s1 out st' tr' hm hn hvb hpre hmatch heval
  exact ⟨ms, rss, h1, h2, h3.toOk⟩

/-- `TryRuleOkT` with the pinned obligation. -/
def TryRuleOkTP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (exts : List Clif.ExtFunc) (outB : Nat) (p : Program)
    (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx → ExternsIn f exts →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  (∀ e, f.extern? fn = some e → SigStackOk e.sig outB) →
  tryCallData f (.tryCall fn args et) = .ok data → TermIntPos ctx (.tryCall fn args et) →
  exnTableOpnd f et = .ok (sig, items) →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    st1.nextVreg ≤ st.nextVreg →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms

/-- **The `try_call` roots of `lower_branch` over typed contexts, with pinned calls.** -/
def TryRulesCorrectTP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (exts : List Clif.ExtFunc) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    CallsRefineP Pc F env exts MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryRootRule r = true →
      TryRuleOkTP Rd Pc isem MR env cp exts outB p r

theorem tryRulesCorrectT_of_P {p : Program} (h : TryRulesCorrectTP p) : TryRulesCorrectT p := by
  intro F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot f ctx hctx hext ti fn
    args et data sig items targets info lo st1 hra hd hip he hi hinfo htr hvb cfg hco m n st tr env'
    s1 out st' tr' hm hn hst hfirst hmatch heval
  obtain ⟨ms, h1, h2⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb syms outB
    hR hMR (memRefinesR_of hMem) hout (hCR.toP _) r hr hroot f ctx hctx hext ti fn args et data sig
    items targets info lo st1 hra hd hip he hi hinfo htr hvb cfg hco m n st tr env' s1 out st' tr' hm
    hn hst hfirst hmatch heval
  exact ⟨ms, h1, h2.toOk⟩

/-- `TryIndRuleOkT` with the pinned obligation. -/
def TryIndRuleOkTP (Rd : BitVec 64 → Prop)
    (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop) (isem : Sem) (MR : MemRelT)
    (env : Clif.Env) (cp : Clif.Program) (sigs : List Clif.Signature) (p : Program) (r : Rule) :
    Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxT f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (sig : Clif.Signature) (items : List (Option Nat)) (targets : List Label) (info : TryInfo)
    (lo st1 : LState),
  tryCallData f (.tryCallIndirect callee args et) = .ok data →
  TermIntPos ctx (.tryCallIndirect callee args et) →
  exnTableOpnd f et = .ok (sig, items) → sig ∈ sigs →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → tryInfoOf sig items targets = some info →
  tryRegsOf sig lo = some (ctx.tryRegs, st1) → ValsBelow ctx lo →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    st1.nextVreg ≤ st.nextVreg →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms

/-- **The `try_call_indirect` root of `lower_branch` over typed contexts, with pinned calls**,
under guarded memory forms and an outgoing area that holds the stack arguments of `sigs`. -/
def TryIndRulesCorrectTP (p : Program) : Prop :=
  ∀ (Rd : BitVec 64 → Prop) (Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop)
    (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program)
    (sigs : List Clif.Signature) (sb : Nat) (syms : String → Option Nat) (outB : Nat),
    Refines F isem → MRStable F MR → MemRefinesR Rd F sb syms isem → OutArgsOk F outB MR →
    IndStack sigs outB → IndCallsRefineP Pc env sigs MR isem →
    ∀ r ∈ p.rulesOf TId.lower_branch, tryIndRootRule r = true →
      TryIndRuleOkTP Rd Pc isem MR env cp sigs p r

theorem tryIndRulesCorrectT_of_P {p : Program} (h : TryIndRulesCorrectTP p) :
    TryIndRulesCorrectT p := by
  intro F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR r hr hroot f ctx hctx ti
    callee args et data sig items targets info lo st1 hd hip he hsig hi hinfo htr hvb cfg hco m n
    st tr env' s1 out st' tr' hm hn hst hfirst hmatch heval
  obtain ⟨ms, h1, h2⟩ := h (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp sigs sb syms outB
    hR hMR (memRefinesR_of hMem) hout hIstk (hCR.toP _) r hr hroot f ctx hctx ti callee args et
    data sig items targets info lo st1 hd hip he hsig hi hinfo htr hvb cfg hco m n st tr env' s1
    out st' tr' hm hn hst hfirst hmatch heval
  exact ⟨ms, h1, h2.toOk⟩

/-! ## The dispatchers -/

set_option maxRecDepth 20000 in
/-- **The typed statement dispatcher with pinned obligations** (`lowerInstOk_of_rulesT` with
`LowerInstOkP`: the integer and float rule families' contracts under the read guard `Rd` —
`MemRefinesR Rd`, `MemRefinesFP Rd` — and the pinned calls). -/
theorem lowerInstOkP_of_rulesT (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hnE : NonEUnmatchableT program) (hcalls : CallRulesCorrectTP program)
    (hind : IndRulesCorrectTP program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) {outB : Nat}
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
      inst hi hc trivial cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  have har : floatArithRootRule r = true → ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧
      out = .regsVec rss ∧ LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
    intro hfa
    obtain ⟨ms, rss, h1, h2, h3⟩ := hFT F isem MR env cp hR hMR r hr hfa f ctx hctx.inv ii info
      inst hi hc trivial cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb hfirst hmatch heval
    exact ⟨ms, rss, h1, h2, h3.toP⟩
  cases hroot : closureRoot r
  · exact absurd hmatch (lower_nonroot_nomatchT_calls hctx.inv hsc hctx.calls hi hc hr
      (by rw [← closureRoot_eq]; exact hroot) cfg m (st, tr) env' s1)
  cases hE : Compile.instE inst
  · cases hfm : floatMoveRootRule r
    · cases hfmem : floatMemRootRule r
      · cases hfa : floatArithRootRule r
        · by_cases hsel : r.id = 971 ∧ FloatSelect inst
          · obtain ⟨ms, rss, h1, h2, h3⟩ := (hT F isem MR env cp hR hMR).2 r hr hsel.1 f ctx
              hctx.inv ii info inst hi hc hsel.2 cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb
              hfirst hmatch heval
            exact ⟨ms, rss, h1, h2, h3.toP⟩
          · exact absurd hmatch (hnE r hr hroot hfm hfmem hfa f ctx hctx hsc ii info inst hi hc hE
              (fun h1 h2 => hsel ⟨h1, h2⟩) hst cfg m st tr env' s1 hfirst)
        · exact har hfa
      · exact hmF hfmem
    · exact hmv hfm
  · cases hcall : callRootRule r
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
          f ctx hctx ii info inst hi hc hE hsig cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb
          hfirst hmatch heval
    · exact hcalls Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hcall f ctx
        hctx hnorm ii info inst hi hc hE hstk cfg hco m n st tr env' s1 out st' tr2 hm1 hn1 hvb
        hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOkP_of_rulesT` for the backend's own call (`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOkP_runTermT (hrules : LowerRulesCorrectTI program)
    (hT : LowerRulesCorrectT program) (hFT : LowerRulesCorrectFT program)
    (hnE : NonEUnmatchableT program) (hcalls : CallRulesCorrectTP program)
    (hind : IndRulesCorrectTP program) (hmem : MemRulesCorrectRTI program)
    (hmemF : MemRulesCorrectRT program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefineP Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefineP Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) (hsc : InstScopeT ctx) {outB : Nat}
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
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOkP_of_rulesT hrules hT hFT hnE hcalls hind hmem
      hmemF hR hMR hcr hicr hMem hFP hctx hsc hout hnorm hMRo hi hc hsig hIstk hst hstk rfl (by omega)
      hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

theorem tryOkP_of_rulesT {p : Program} (hp : Data p) (hrules : TryRulesCorrectTP p)
    (hun : TryUnmatchableT p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hcr : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hip : TermIntPos ctx (.tryCall fn args et)) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
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
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti fn args et data targets hd hi cfg m (st, tr)
      env' s1)
  · exact hrules Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hroot f ctx
      hctx hext ti fn args et data sig items targets info lo st1 hra hd hip he hi hinfo htr hvb cfg
      hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `tryOkP_of_rulesT` for the exported program and the backend's call on a `try_call`. -/
theorem tryOkP_runTermT (hrules : TryRulesCorrectTP program) (hun : TryUnmatchableT program)
    {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefineP Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hip : TermIntPos ctx (.tryCall fn args et)) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st' ms := by
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
    obtain ⟨ms, h1, h2⟩ := tryOkP_of_rulesT data_program hrules hun hR hMR hMem hout hcr hctx hext
      hra hd hip he hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

theorem tryIndOkP_of_rulesT {p : Program} (hp : Data p) (hrules : TryIndRulesCorrectTP p)
    (hun : TryIndUnmatchableT p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hIstk : IndStack sigs outB) (hcr : IndCallsRefineP Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {ti callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hip : TermIntPos ctx (.tryCallIndirect callee args et))
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
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
  cases hroot : tryIndRootRule r
  · exact absurd hmatch
      (hun r hr hroot f ctx hctx ti callee args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hcr r hr hroot f
      ctx hctx ti callee args et data sig items targets info lo st1 hd hip he hsig hi hinfo htr hvb
      cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `tryIndOkP_of_rulesT` for the exported program and the backend's call on a
`try_call_indirect`. -/
theorem tryIndOkP_runTermT (hrules : TryIndRulesCorrectTP program)
    (hun : TryIndUnmatchableT program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {sigs : List Clif.Signature} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hIstk : IndStack sigs outB)
    (hcr : IndCallsRefineP Pc env sigs MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    {ti callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hip : TermIntPos ctx (.tryCallIndirect callee args et))
    (he : exnTableOpnd f et = .ok (sig, items)) (hsig : sig ∈ sigs)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOf sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st' ms := by
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
    obtain ⟨ms, h1, h2⟩ := tryIndOkP_of_rulesT data_program hrules hun hR hMR hMem hout hIstk hcr
      hctx hd hip he hsig hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

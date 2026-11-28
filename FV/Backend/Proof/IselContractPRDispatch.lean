import FV.Backend.Proof.IselContractPR

/-!
# The pinned dispatchers with the call contracts with registers (#753, stage R2)

`lowerInstOkP_of_rules`, `tryOkP_of_rules`, `tryIndOkP_of_rules` and their `runTerm` forms
(`IselContractP`) with the rule families and call contracts of `IselContractPR`
(`CallRulesCorrectPR`, …, `CallsRefinePR`, `IndCallsRefinePR`): every `lower`/`lower_branch` call
of the backend satisfies the pinned obligation under the contracts with registers.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **`lower` with pinned obligations**: every rule family under its contract (`LowerRulesCorrect`,
`MemRulesCorrectR` under `MemRefinesR Rd`, the call rules under the pinned contracts). -/
theorem lowerInstOkPR_of_rules {p : Program} (hp : Data p) (hrules : LowerRulesCorrect p)
    (hex : ExcludedUnmatchable p) (hcalls : CallRulesCorrectPR p) (hind : IndRulesCorrectPR p)
    (hmem : MemRulesCorrectR p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {exts : List Clif.ExtFunc} (hcr : CallsRefinePR Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefinePR Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hE : Compile.functionE f = true)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hIstk : IndStack sigs outB)
    (hstk : ∀ fn args e, inst = .call fn args → f.extern? fn = some e → SigStackOk e.sig outB)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId} (hvb : ValsBelow ctx st)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧
      LowerInstOkP Rd Pc isem MR env cp ctx inst info.results st rss st' ms := by
  change 1002 + (p.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, hpre0, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco hp.t686 term_686_kind rfl h
  have hr : r ∈ p.rulesOf TId.lower := by
    change r ∈ p.rulesOf 686; rw [hsplit]; simp
  have hfirst : ∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ii]).run (st, tr) = .ok (none, s') := by
    intro pre post hsp r' hr'
    have hnd : (pre0 ++ r :: post0).Nodup := hsplit ▸ lower_rules_nodup hp
    have hpre := prefix_unique_of_nodup hnd (hsplit.symm.trans hsp)
    subst hpre
    obtain ⟨m', hm', s', h'⟩ := hpre0 r' hr'
    exact ⟨m', by omega, s', h'⟩
  simp only [Prod.mk.injEq] at hs
  rw [← hs.1] at heval
  cases hroot : closureRoot r
  · exact absurd hmatch (hex r hr hroot f ctx hctx hE ii info inst hi hc cfg m (st, tr) env' s1)
  · cases hcall : callRootRule r
    · cases hind' : indRootRule r
      · cases hm : memRootRule r
        · obtain ⟨ms, rss, h1, h2, h3⟩ := hrules F isem MR env cp hR hMR r hr hroot hcall hind' hm f
            ctx hctx ii info inst hi hc cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega)
            hvb hfirst hmatch heval
          exact ⟨ms, rss, h1, h2, h3.toP⟩
        · obtain ⟨ms, rss, h1, h2, h3⟩ := hmem Rd F sb syms isem MR env cp hR hMR hMem r hr hm f ctx
            hctx hMRo ii info inst hi hc cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega)
            hvb hfirst hmatch heval
          exact ⟨ms, rss, h1, h2, h3.toP⟩
      · exact hind Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hicr r hr hind' f
          ctx hctx ii info inst hi hc
          hsig cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval
    · exact hcalls Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hcall f ctx
        hctx hnorm ii info inst hi hc hstk
        cfg hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hvb hfirst hmatch heval

set_option maxRecDepth 20000 in
/-- `lowerInstOkPR_of_rules` for the exported program and the backend's own call
(`runTerm ctx "lower" [.inst ii]`). -/
theorem lowerInstOkPR_runTerm (hrules : LowerRulesCorrect program)
    (hex : ExcludedUnmatchable program) (hcalls : CallRulesCorrectPR program)
    (hind : IndRulesCorrectPR program) (hmem : MemRulesCorrectR program) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR)
    {exts : List Clif.ExtFunc} (hcr : CallsRefinePR Pc F env exts MR isem)
    {sigs : List Clif.Signature} (hicr : IndCallsRefinePR Pc env sigs MR isem)
    (hMem : MemRefinesR Rd F sb syms isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hnorm : ExternsIn f exts) (hE : Compile.functionE f = true)
    (hMRo : MemRelOk F sb syms f MR) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hsig : IndSigOk f sigs inst) (hIstk : IndStack sigs outB)
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
    obtain ⟨ms, rss, h1, h2, h3⟩ := lowerInstOkPR_of_rules data_program hrules hex hcalls hind hmem
      hR hMR hcr hicr hMem hctx hout hnorm hE hMRo hi hc hsig hIstk hstk rfl (by omega) hvb ha
    exact ⟨ms, rss, by simpa using h1, h2, h3⟩

theorem tryOkPR_of_rules {p : Program} (hp : Data p) (hrules : TryRulesCorrectPR p)
    (hun : TryUnmatchable p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hcr : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
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
  · exact absurd hmatch (hun r hr hroot f ctx hctx ti fn args et data targets hd hi cfg m (st, tr) env' s1)
  · exact hrules Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hcr r hr hroot f ctx hctx
      hext ti fn args et data sig items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st
      tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
theorem tryOkPR_runTerm (hrules : TryRulesCorrectPR program) (hun : TryUnmatchable program)
    {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
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
    obtain ⟨ms, h1, h2⟩ := tryOkPR_of_rules data_program hrules hun hR hMR hMem hout hcr hctx hext
      hra hd he hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

theorem tryIndOkPR_of_rules {p : Program} (hp : Data p) (hrules : TryIndRulesCorrectPR p)
    (hun : TryIndUnmatchable p) {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {F : BitVec 64 → Prop}
    {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sigs : List Clif.Signature}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    (hIstk : IndStack sigs outB) (hcr : IndCallsRefinePR Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
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
      ctx hctx ti callee args et data sig items targets info lo st1 hd he hsig hi hinfo htr hvb cfg
      hco m n st tr env' s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval

set_option maxRecDepth 20000 in
theorem tryIndOkPR_runTerm (hrules : TryIndRulesCorrectPR program) (hun : TryIndUnmatchable program)
    {Rd : BitVec 64 → Prop} {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {sigs : List Clif.Signature} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hIstk : IndStack sigs outB)
    (hcr : IndCallsRefinePR Pc env sigs MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {ti callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
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
    obtain ⟨ms, h1, h2⟩ := tryIndOkPR_of_rules data_program hrules hun hR hMR hMem hout hIstk hcr
      hctx hd he hsig hi hinfo htr hvb rfl (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

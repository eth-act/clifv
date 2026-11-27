import FV.Backend.Proof.LowerContractTC
import FV.Backend.Proof.IselCtlCallTFPR

/-!
# The typed `try_call` dispatcher under the call contracts with registers (#753, stage R2)

`tryOkC_of_rules`, `tryOkC_runTerm`, `tryCallsTC_of_rules` (`LowerContractTC`) from the proven
`try_call` family with registers (`TryRulesCorrectTFPR`, `tryRulesCorrectTFPR_program`) under the
unpinned callee contract with registers (`CallsRefinePR` at the trivial pin): `tryOkCR_of_rules`,
`tryOkCR_runTerm`, `tryCallsTCR_of_rules`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64 Backend.Proof.Driver

theorem tryOkCR_of_rules {p : Program} (hp : Data p) (hrules : TryRulesCorrectTFPR p)
    (hun : TryUnmatchableTC p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {exts : List Clif.ExtFunc}
    (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms isem) (hFP : MemRefinesFP (fun _ => True) F sb isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {targets : List Label}
    {info : TryInfo} {lo st1 : LState} (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (p.rulesOf TId.lower_branch).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hst : st1.nextVreg ≤ st.nextVreg)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty TId.lower_branch [.inst ti, .labels targets]).run
      (st, tr) = .ok (some out, (st', tr'))) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkC isem MR env cp ctx (.call fn args) info st st' ms := by
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
  · obtain ⟨ms, h1, h2⟩ := hrules (fun _ => True) (fun _ _ _ _ => True) F isem MR env cp exts sb
      syms outB hR hMR (memRefinesR_of hMem) hFP hout hcr r hr hroot f ctx hctx hext ti fn
      args et data sig items targets info lo st1 hra hd he hi hinfo htr hvb cfg hco m n st tr env'
      s1 out st' tr2 (by omega) (by omega) hst hfirst hmatch heval
    exact ⟨ms, h1, h2.toOk⟩

set_option maxRecDepth 20000 in
/-- `tryOkCR_of_rules` for the exported program and the backend's call on a typed `try_call`. -/
theorem tryOkCR_runTerm
    {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {exts : List Clif.ExtFunc} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefines F sb syms isem)
    (hFP : MemRefinesFP (fun _ => True) F sb isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    (hcr : CallsRefinePR (fun _ _ _ _ => True) F env exts MR isem) {f : Clif.Function} {ctx : Ctx} (hctx : CallCtxT f ctx)
    (hext : ExternsIn f exts) {ti : Nat} {fn : Clif.FnRef}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {targets : List Label} {info : TryInfo} {lo st1 : LState}
    (hra : ∀ e, f.extern? fn = some e → SigStackOk e.sig outB)
    (hd : tryCallDataC f (.tryCall fn args et) = .ok data)
    (he : exnTableOpndC f et = .ok (sig, items))
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hinfo : tryInfoOf sig items targets = some info)
    (htr : tryRegsOfC sig lo = some (ctx.tryRegs, st1)) (hvb : ValsBelow ctx lo)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId} (hst : st1.nextVreg ≤ st.nextVreg)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    ∃ ms, st'.emitted = st.emitted ++ ms.toArray ∧
      LowerTryOkC isem MR env cp ctx (.call fn args) info st st' ms := by
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
    obtain ⟨ms, h1, h2⟩ := tryOkCR_of_rules data_program tryRulesCorrectTFPR_program
      tryUnmatchableTC_program hR hMR hMem hFP hout hcr hctx hext hra hd he hi hinfo htr hvb rfl
      (by omega) hst ha
    exact ⟨ms, by simpa using h1, h2⟩

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- **From the proven typed `try_call` family to the driver's typed `try_call` calls** in a
float-capable context (under the callee contract for `f`'s externs and the float accesses'
`MemRefinesFP`). -/
theorem tryCallsTCR_of_rules {F : BitVec 64 → Prop} {sem : Sem}
    {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {f : Clif.Function} {ctx : Ctx}
    (hR : Refines F sem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat} (hMem : MemRefines F sb syms sem)
    (hFP : MemRefinesFP (fun _ => True) F sb sem)
    {outB : Nat} (hout : OutArgsOk F outB MR) (hcr : CallsRefinePR (fun _ _ _ _ => True) F env (f.externs.map (·.2)) MR sem)
    (hctx : CtxInvT f ctx) : TryCallsTC f ctx sem MR env p outB := by
  intro ti fn args et data sig items targets info trs lo st1 out st' tr hra hd he hph
    hinfo hregs hvb hrun
  have hctx' := callCtxT_tryCtx hctx hph data trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hregs' : tryRegsOfC sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := hregs
  have hvb' : ValsBelow (tryCtx ctx ti data trs) lo := hvb
  obtain ⟨ms, hem, hok⟩ := tryOkCR_runTerm hR hMR hMem hFP hout hcr hctx' (externsIn_self f) hra
    hd he hi hinfo hregs' hvb' (st := { st1 with emitted := #[] }) (Nat.le_refl _) hrun
  have : ms = st'.emitted.toList := by
    simp only [Array.empty_append] at hem; rw [hem, List.toList_toArray]
  rw [← this]; exact hok

end Backend.Proof.Driver

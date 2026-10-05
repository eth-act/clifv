import FV.Backend.Proof.IselCovModel
import FV.Backend.Proof.IselCovClean
import FV.Backend.Proof.IselCovTab
import FV.Backend.Proof.IselFlow
import FV.Backend.Proof.LowerContract

/-!
# Form coverage of the ISLE lowering (V3): the driver's calls

The abstract interpretation (`soundAt` with `covModel`, the table `covTab` and its root checks)
applied to the driver's three ISLE calls: a statement's `lower` (`stmt_cov`: everything emitted
is covered, and the result registers of an instruction with results are int vregs), a
terminator's `lower`/`lower_branch` (`termCall_cov`) and a `try_call`'s `lower_branch`
(`tryCall_cov`). Rules that are not checked roots never match (`lower_nonroot_nomatch`,
`lower_term_nomatch`; `nop`'s rule 587 has no results).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64

theorem covSince_refl (s : LState) : CovSince s s := ⟨[], by simp, by simp⟩

theorem γ_c0_inst {f : Clif.Function} {ctx : Ctx} (i : Nat) : γ f ctx AW.c0 (.inst i) :=
  ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩

theorem γ_c0_labels {f : Clif.Function} {ctx : Ctx} (ls : List Label) : γ f ctx AW.c0 (.labels ls) :=
  ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩

theorem holds_inst {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) :
    Holds2 f ctx [.xv .inst] [.inst ii] :=
  ⟨⟨⟨ii, info, inst, rfl, hi, hc, hctx.data _ _ _ hi hc⟩, rfl, rfl⟩, trivial⟩

set_option maxRecDepth 100000 in
/-- **A statement's lowering is covered**: every instruction it emits is covered, and the result
registers of an instruction with results are int vregs. -/
theorem stmt_cov (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hcl : Cov.Clean ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    CovSince s s' ∧ ∀ rss, out = some (.regsVec rss) → info.results ≠ [] →
      ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n, r = .vreg n .int := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have sa := soundAt (hctx := hctx) (md := covModel hLI hctx hcl s) (cfg := {}) (tab := covTab)
    rfl covTab_ok 1000000
  have hins := holds_inst hctx hi hc
  have hrulesTop : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor apre aOracle [.xv .inst] AW.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp covStmtTop_ok rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with hcr | ha
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · exact .inl ha
  refine ⟨(sa.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] AW.top [.inst ii] s #[] out s' tr'
    data_program.t686 term_686_kind hrulesTop hins (covSince_refl s) happ).1, ?_⟩
  intro rss hout hres rs hrs r hr
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor apre aOracle [.xv .inst] (.flat 1 true) rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp covStmt_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (hcr | h587) | ha
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := pinned_names hctx hi hc hop.1 kind_nullAry kind_nop hm
      rw [variantNames_Nop] at hn
      have hnop := instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  obtain ⟨-, hv⟩ := sa.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] (.flat 1 true) [.inst ii] s #[]
    out s' tr' data_program.t686 term_686_kind hrules hins (covSince_refl s) happ
  subst hout
  have hk := (hv _ rfl).1 r (mem_regsVec hrs hr)
  rcases kind_cases r with h1 | h1 | h1 | h1
  · obtain ⟨n, rfl⟩ := kind_int h1
    exact ⟨n, rfl⟩
  all_goals rw [h1] at hk; exact (hk (by decide)).elim

set_option maxRecDepth 100000 in
/-- `lower_branch` in a context with `CtxInv`/`Clean`: everything emitted is covered. -/
theorem branch_cov (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    CovSince s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have sa := soundAt (hctx := hctx) (md := covModel hLI hctx hcl s) (cfg := {}) (tab := covTab)
    rfl covTab_ok 1000000
  have hins : Holds2 f ctx [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
  exact (sa.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [AW.c0, AW.c0] AW.top _ s #[]
    out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp covBranch_ok rl hrl)) hins (covSince_refl s) happ).1

set_option maxRecDepth 100000 in
/-- **A terminator's lowering is covered** (`lower` on `return`/`trap`, `lower_branch` on a
branch). -/
theorem termCall_cov (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hcl : Cov.Clean ctx) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) : CovSince s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hctx' := ctxInv_termCtx hctx hph data
  have hcl' := clean_termCtx hcl hd ti
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) → CovSince s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program covTab aext actor apre aOracle [AW.c0] AW.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp covTerm_ok rl hrl
        simp only [termRootRule] at hroot
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    have sa := soundAt (hctx := hctx') (md := covModel hLI hctx' hcl' s) (cfg := {}) (tab := covTab)
      rfl covTab_ok 1000000
    exact (sa.root T.lower.ret T.lower.id T.lower _ _ [AW.c0] AW.top [.inst ti] s #[] out s' tr'
      data_program.t686 term_686_kind hrules ⟨γ_c0_inst ti, trivial⟩ (covSince_refl s) happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_cov hLI hctx' hcl' h
  | brif c a b => exact branch_cov hLI hctx' hcl' h
  | brTable x d tb => exact branch_cov hLI hctx' hcl' h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

/-- **A `try_call`'s lowering is covered** (`lower_branch` in the `try_call` context). -/
theorem tryCall_cov (hLI : LogicImmComplete) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hcl : Cov.Clean ctx) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data) {trs : List Reg × List Reg}
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) : CovSince s s' := by
  have h' := ctxInv_termCtx hctx hph data
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { h' with }
  exact branch_cov hLI hctx' (clean_tryCtx hcl hd ti trs) h

end Backend.Proof.Driver

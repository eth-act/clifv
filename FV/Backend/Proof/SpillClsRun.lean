import FV.Backend.Proof.SpillClsModel

/-!
# The class facts of the driver's ISLE calls (V4 classes)

`soundAtC` with `clsModel` and `clsTab` applied to the driver's three ISLE calls, as in
`IselCovDriver`: a statement's `lower` (`stmt_cls`), a terminator's `lower`/`lower_branch`
(`termCall_cls`), a `try_call`'s `lower_branch` (`tryCall_cls`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

theorem holds_inst_cls (s : LState) (i : Nat) : Holds2 γC s [⟨1, true⟩] [.inst i] :=
  ⟨fun _ r hr => by simp [V.regsIn] at hr, trivial⟩

set_option maxRecDepth 100000 in
/-- **A statement's lowering** keeps `ClsIs`; its result (of an instruction with results) has
registers of their classes. -/
theorem stmt_cls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) (hIs : ClsIs ctx s s) :
    ClsIs ctx s s' ∧ ∀ v, out = some v → info.results ≠ [] → GoodV s'.classes v := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have sa := soundAtC (md := clsModel hcl s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
  have hrulesTop : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] FA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hf
    rcases hf with hcr | ⟨ha, -⟩
    · exact .inr (lower_nonroot_nomatch hctx hi hc hrl hcr)
    · exact .inl ha
  refine ⟨(sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] FA.top [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrulesTop (holds_inst_cls s ii) hIs happ).1, ?_⟩
  intro v hout hres
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at hf
    rcases hf with hcr | ⟨-, h587 | ha⟩
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
  exact (sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩ [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrules (holds_inst_cls s ii) hIs happ).2 v hout (by decide)

set_option maxRecDepth 100000 in
/-- `lower_branch` in a context with `CtxInv`/`Clean` keeps `ClsIs`. -/
theorem branch_cls {ctx : Ctx} (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label} {s : LState}
    {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr))
    (hIs : ClsIs ctx s s) : ClsIs ctx s s' := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have sa := soundAtC (md := clsModel hcl s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
  have hins : Holds2 γC s [⟨1, true⟩, FA.c0] [.inst ti, .labels targets] :=
    ⟨fun _ r hr => by simp [V.regsIn] at hr, fun _ r hr => by simp [V.regsIn] at hr, trivial⟩
  exact (sa.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [⟨1, true⟩, FA.c0] FA.top _ s
    #[] out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp clsBranch_ok rl hrl)) hins hIs happ).1

set_option maxRecDepth 100000 in
/-- **A terminator's lowering** (`lower` on `return`/`trap`, `lower_branch` on a branch) keeps
`ClsIs`. -/
theorem termCall_cls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) (hcl : Cov.Clean ctx)
    {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {data : V} (hd : termData (abiTerm f t) = .ok data) {targets : List Label}
    {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : termCallF ctx ti data t targets s = .ok (out, s', tr))
    (hIs : ClsIs (termCtx ctx ti data) s s) : ClsIs (termCtx ctx ti data) s s' := by
  have hti : ti < ctx.insts.size := (Array.getElem?_eq_some_iff.mp hph).1
  have hcl' := Cov.clean_termCtx hcl hd ti
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      ClsIs (termCtx ctx ti data) s s' := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRuleC program clsTab false [⟨1, true⟩] FA.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp clsTerm_ok rl hrl
        simp only [hroot, Bool.not_true, Bool.false_or] at hf
        exact .inl hf
    have sa := soundAtC (md := clsModel hcl' s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
    exact (sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] FA.top [.inst ti] s #[] out s' tr'
      data_program.t686 term_686_kind hrules (holds_inst_cls s ti) hIs happ).1
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_cls hcl' h hIs
  | brif c a b => exact branch_cls hcl' h hIs
  | brTable x d tb => exact branch_cls hcl' h hIs
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

/-- **A `try_call`'s lowering** keeps `ClsIs`. -/
theorem tryCall_cls {f : Clif.Function} {ctx : Ctx} (hcl : Cov.Clean ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hd : tryCallData f t = .ok data) {trs : List Reg × List Reg}
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr))
    (hIs : ClsIs (tryCtx ctx ti data trs) s s) : ClsIs (tryCtx ctx ti data trs) s s' :=
  branch_cls (Cov.clean_tryCtx hcl hd ti trs) h hIs

end Backend.Proof.Spill

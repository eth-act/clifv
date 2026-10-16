import FV.Backend.Proof.StockCoverageModel
import FV.Backend.Proof.IselCovDriver
import FV.Backend.Proof.SpillLocalForms

namespace Backend.Stock.Proof.Coverage.Emission
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program

/-- The existing checked Stock analysis instantiated with emitted-form
coverage. This model is derived from real helpers and unchanged tables. -/
def model {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (clean : Clean (sourceIdentityCtx ctx)) (initial : LState) : Coverage.Model program f ctx where
  Is := fun st => CovSince initial st.base
  source := covModel logicImmComplete mapped.identityView clean initial
  ctor := by
    intro t term lookup as vs value st next held invariant pre run
    have both : (term.id != TId.opportunistic_def) = true ∧ apre term.id as = true := by
      simpa only [noOpportunityPre,Bool.and_eq_true] using pre
    have allowed := both.2
    exact ctor_emission_coverage mapped logicImmComplete held allowed run invariant
  oracle := oracle_sound _

private theorem stock_lower_nonroot_nomatch {f : Clif.Function} {ctx original : Ctx}
    (view : DFGViewEq ctx original) (hctx : CtxInv f original) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : original.insts[ii]? = some info)
    (hc : info.clif = some inst) {r : Rule} (hr : r ∈ program.rulesOf TId.lower)
    (hroot : closureRootIds.contains r.id = false) :
    ∀ m s0 env s1, (matchRule program (Stock.sem ctx) {} m r [.inst ii]).run s0 ≠
      .ok (some env, s1) := by
  intro m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOk_program r hr
  simp only [exclOk, hroot, Bool.false_or] at hok
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    rw [stock_matchArgs_source view] at ha
    split at hok
    · rename_i q hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact fails_sound hctx q .inst _ _ _ _ hok
        ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
    · cases hok


private theorem named_run_apply {ctx : Ctx} {name : String} {args : List V}
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx name args before = .ok (out, after, trace)) :
    ∃ (term : Term) (finalTrace : Array RuleId), program.termByName? name = some term ∧
      (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config)) term.ret term.id args).run
        (before, #[]) = .ok (out, after, finalTrace) := by
  unfold Stock.runTerm at run
  cases actual : Isle.Interp.run program (Stock.sem ctx) {} name args before with
  | error e => rw [actual] at run; cases run
  | ok result =>
    rw [actual] at run
    cases run
    unfold Isle.Interp.run at actual
    cases lookup : program.termByName? name with
    | none => simp only [lookup] at actual; cases actual
    | some term =>
      simp only [lookup] at actual
      cases lowered : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          term.ret term.id args).run (before, #[]) with
      | error e => simp only [lowered, bind, Except.bind] at actual; cases actual
      | ok result =>
        rcases result with ⟨out, after, trace⟩
        simp only [lowered, bind, Except.bind, pure, Except.pure] at actual
        cases actual
        exact ⟨term, trace, rfl, lowered⟩


/-- Every actual statement root emits covered instruction forms under the
original mapped source invariant. Failed matches and helper calls are included;
no emitted-form certificate or extra acceptance check is supplied. -/
theorem stock_statement_emission_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (out,after,trace)) :
    CovSince before.base after.base := by
  obtain ⟨term,finalTrace,lookup,lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := model mapped clean before.base
  have cert := Coverage.soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have input := holds_inst mapped.identityView (show (sourceIdentityCtx ctx).insts[ii]? = some info from source) original
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] AW.top r = true ∨
        ∀ fuel st env next,(matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠ .ok (some env,next) := by
    intro r member
    have checked := List.all_eq_true.mp stock_noOpportunity_roots_checked.1 r member
    simp only [Bool.or_eq_true,Bool.not_eq_true'] at checked
    rcases checked with excluded | checked
    · right
      intro fuel st env next
      exact stock_lower_nonroot_nomatch (show DFGViewEq ctx (sourceIdentityCtx ctx) from ⟨rfl,rfl,rfl,rfl,rfl⟩)
        mapped.identityView source original member excluded fuel st env next
    · exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] AW.top [.inst ii]
    before #[] out after finalTrace data_program.t686 term_686_kind rules input (covSince_refl _) lowered).1

/-- Actual branch roots emit covered forms through the same unchanged checked
table. No source/target shape or caller emitted-instruction certificate is added. -/
theorem stock_branch_emission_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {targets : List Label} {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets] before = .ok (out,after,trace)) :
    CovSince before.base after.base := by
  obtain ⟨term,finalTrace,lookup,lowered⟩ := named_run_apply run
  rw [program_termByName_lower_branch] at lookup
  cases lookup
  let md := model mapped clean before.base
  have cert := Coverage.soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have input : Holds2 f (sourceIdentityCtx ctx) [AW.c0,AW.c0] [.inst ti,.labels targets] :=
    ⟨γ_c0_inst ti,γ_c0_labels targets,trivial⟩
  exact (cert.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [AW.c0,AW.c0] AW.top _
    before #[] out after finalTrace data_program.t687 term_687_kind
    (fun r member => .inl (List.all_eq_true.mp stock_noOpportunity_roots_checked.2.2 r member))
    input (covSince_refl _) lowered).1

end Backend.Stock.Proof.Coverage.Emission

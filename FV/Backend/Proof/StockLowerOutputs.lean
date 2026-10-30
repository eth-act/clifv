import FV.Backend.Proof.StockCoverageRoots
import FV.Backend.Proof.StockLowerProgress

/-!
# Stock statement outputs are int registers

The baseline statement coverage (`stmt_cov`) on the Stock coverage model: every rule of `lower`
that is a checked root has output `.flat 1 true` (`stock_covStmt_ok`), the other roots do not match
a scalar statement with results (the nop rule by its opcode, the calls by `lower_diverging_args_fail`),
so a successful Stock `lower` run of such a statement returns only int vregs. `bindResults` needs
this to alias each result value to its register.
-/

namespace Backend.Stock.Proof.Coverage
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
  Backend.Stock.Proof
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every checked root of `lower` except the nop rule and the calls has int-vreg outputs. -/
theorem stock_covStmt_ok : (program.rulesOf TId.lower).all (fun r => !closureRootIds.contains r.id ||
    r.id == 587 || r.id == 1031 || r.id == 1032 || r.id == 1033 ||
    aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] (.flat 1 true) r) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
/-- The nop rule of `lower` matches on the `Nop` opcode. -/
theorem lower_nop_opcode : (program.rulesOf 686).all (fun r =>
    r.id != 587 || sourceRuleOpcode program r == some VIdx.Opcode.Nop) = true := by
  rw [data_program.r686]
  decide +kernel

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

/-- A rule whose arguments fail on the baseline semantics never matches on Stock's. -/
theorem stock_nomatch_of_argsFail {ctx : Ctx} {r : Rule} {vs : List V}
    (fail : ArgsFail program (Backend.sem ctx) r vs) :
    ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r vs).run st ≠
      .ok (some env, next) := by
  intro fuel st env next matched
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, -⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    exact fail _ _ args

set_option maxRecDepth 100000 in
/-- **Stock statement outputs are int vregs.** A successful Stock `lower` run of a scalar statement
with results returns only int vregs. -/
theorem stock_stmt_int_out {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (clean : Clean (sourceIdentityCtx ctx))
    (noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst), ctx.insts[j]? = some info →
      info.clif = some cl → (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load")
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[ii]? = some info)
    (original : info.clif = some inst) (scalar : LowerProjection.ScalarNames inst)
    (results : info.results ≠ []) {before after : State} {rss : List (List Reg)}
    {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (some (.regsVec rss), after, trace)) :
    ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n, r = .vreg n .int := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := model mapped clean before.opportunistic
  have cert := soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have source' : (sourceIdentityCtx ctx).insts[ii]? = some info := source
  have input := holds_inst mapped.identityView source' original
  have diverging : ∀ r ∈ program.rulesOf TId.lower, r.id ∈ LowerProjection.lowerDiverging →
      ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠
        .ok (some env, next) := fun r member hdiv =>
    stock_nomatch_of_argsFail (LowerProjection.lower_diverging_args_fail mapped noLoad source original
      scalar.names scalar.extend r member hdiv)
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] (.flat 1 true) r = true ∨
        ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠
          .ok (some env, next) := by
    intro r member
    have checked := List.all_eq_true.mp stock_covStmt_ok r member
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at checked
    rcases checked with ((((excluded | nop) | call) | call) | call) | checked
    · exact .inr (stock_lower_nonroot_nomatch view mapped.identityView source' original member excluded)
    · refine .inr (stock_nomatch_of_argsFail ?_)
      have opcode := List.all_eq_true.mp lower_nop_opcode r member
      simp only [nop, bne_self_eq_false, Bool.false_or, beq_iff_eq] at opcode
      refine LowerProjection.argsFail_of_name mapped opcode Driver.variantNames_Nop (by decide) source original ?_
      intro named
      have isNop := Driver.instNames_nop named
      subst isNop
      obtain ⟨tys, hty, -, hlen⟩ := mapped.identityView.resTys ii info .nop source' original
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact results (List.eq_nil_of_length_eq_zero hlen)
    all_goals first
      | exact .inl checked
      | exact .inr (diverging r member (by simp [call, LowerProjection.lowerDiverging]))
  have hv := (cert.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] (.flat 1 true) [.inst ii]
    before #[] _ after finalTrace data_program.t686 term_686_kind rules input rfl lowered).2 _ rfl
  intro rs hrs r hr
  have hk := hv.1 r (mem_regsVec hrs hr)
  rcases kind_cases r with h1 | h1 | h1 | h1
  · obtain ⟨n, rfl⟩ := kind_int h1
    exact ⟨n, rfl⟩
  all_goals rw [h1] at hk; exact (hk (by decide)).elim

end Backend.Stock.Proof.Coverage

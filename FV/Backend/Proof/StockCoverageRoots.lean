import FV.Backend.Proof.StockCoverageModel
import FV.Backend.Proof.IselCovDriver
import FV.Backend.Proof.StockConstantRoot
import FV.Backend.Proof.StockResults

/-! Actual named instruction-selection roots preserve remembered definitions.
Reuse the checked summaries and pure source-rule exclusions; no root-specific
semantic certificate is assumed by callers. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

/-- A successful actual source-statement root leaves the remembered table
unchanged, including selected helpers and failed-match rollback. -/
theorem statement_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (out, after, trace)) :
    after.opportunistic = before.opportunistic := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := model mapped clean before.opportunistic
  have cert := soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have input := holds_inst mapped.identityView (show (sourceIdentityCtx ctx).insts[ii]? = some info from source)
    original
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] AW.top r = true ∨
        ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠
          .ok (some env, next) := by
    intro r member
    have checked := List.all_eq_true.mp stock_noOpportunity_roots_checked.1 r member
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at checked
    rcases checked with excluded | checked
    · exact .inr (stock_lower_nonroot_nomatch view mapped.identityView source original member excluded)
    · exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] AW.top [.inst ii]
    before #[] out after finalTrace data_program.t686 term_686_kind rules input rfl lowered).1

/-- Every successful actual branch root retains remembered definitions. The
same fixed branch rule checks admit its real instruction/label arguments. -/
theorem branch_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {targets : List Label} {before after : State} {out : Option V}
    {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets] before =
      .ok (out, after, trace)) : after.opportunistic = before.opportunistic := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower_branch] at lookup
  cases lookup
  let md := model mapped clean before.opportunistic
  have cert := soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have input : Holds2 f (sourceIdentityCtx ctx) [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
  exact (cert.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [AW.c0, AW.c0]
    AW.top _ before #[] out after finalTrace data_program.t687 term_687_kind
    (fun r member => .inl (List.all_eq_true.mp stock_noOpportunity_roots_checked.2.2 r member))
    input rfl lowered).1

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem named_of_apply {ctx : Ctx} {name : String} {term : Term} {args : List V}
    {before after : State} {out : Option V} {trace : Array RuleId}
    (lookup : program.termByName? name = some term)
    (run : (applyTerm program (Stock.sem ctx) {} 1000000 term.ret term.id args).run
      (before, #[]) = .ok (out, after, trace)) :
    Stock.runTerm ctx name args before = .ok (out, after, trace.toList) := by
  unfold Stock.runTerm Isle.Interp.run
  rw [lookup]
  dsimp only
  rw [run]
  rfl

/-- The statement premises come from a nonempty real context build and the
already-proved allocating constant root at the driver's actual fuel. -/
theorem statement_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial after : State)
      (info : IInfo) (trace : List RuleId),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      Stock.runTerm ctx "lower" [.inst 0] sinkState =
        .ok (some (.regsVec [[.vreg 194 .int]]), after, trace) ∧
      after.opportunistic = sinkState.opportunistic := by
  obtain ⟨f, ctx, ranges, initial, info, after, trace, scope, build, source, original,
    results, mappedReg, run⟩ := stock_statement_selectedConstant_built_witness
  have named := named_of_apply program_termByName_lower run
  have mapped := buildCtx_mappedInv scope build
  have clean := clean_stock build
  exact ⟨f, ctx, ranges, initial, after, info, _, scope, build, mapped, clean,
    source, original, mappedReg, named, statement_noOpportunity mapped clean source original named⟩

private def jumpFunction : Clif.Function := {
  name := "stock_branch_preservation"
  sig := {callConv := some .systemV}
  blocks := [{id := 0, term := .jump ⟨1, []⟩}, {id := 1, term := .ret []}] }
private def jumpBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx jumpFunction).toOption.getD (sinkCtx, #[], sinkState)
private def jumpData : V := (Backend.termData (.jump ⟨1, []⟩)).toOption.getD (.op .unit)
private def jumpCtx : Ctx := Driver.termCtx jumpBuilt.1 0 jumpData
private def jumpAfter : State :=
  {jumpBuilt.2.2 with base := jumpBuilt.2.2.base.emit (.jump 1)}
private theorem jump_build : Stock.buildCtx jumpFunction = .ok jumpBuilt := rfl
private theorem jump_scope : LowerScope jumpFunction := lowerScope_of (by decide +kernel)
private theorem jump_run :
    Stock.runTerm jumpCtx "lower_branch" [.inst 0, .labels [1]] jumpBuilt.2.2 =
      .ok (some (.op .unit), jumpAfter, [559, 6, 1139]) := by rfl

/-- A real two-block function emits a nonempty jump chunk through the actual
branch root while retaining its complete remembered-definition table. -/
theorem branch_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial after : State),
      LowerScope f ∧ f.blocks.length = 2 ∧ MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      Stock.runTerm ctx "lower_branch" [.inst 0, .labels [1]] initial =
        .ok (some (.op .unit), after, [559, 6, 1139]) ∧
      after.base.emitted = #[.jump 1] ∧ after.opportunistic = initial.opportunistic := by
  have mapped : MappedCtxInv jumpFunction jumpCtx :=
    (buildCtx_mappedInv jump_scope jump_build).termCtx (by rfl) jumpData
  have data : Backend.termData (.jump ⟨1, []⟩) = .ok jumpData := rfl
  have clean : Clean (sourceIdentityCtx jumpCtx) :=
    clean_termCtx (clean_stock jump_build) data 0
  exact ⟨jumpFunction, jumpCtx, jumpBuilt.2.2, jumpAfter, jump_scope, rfl, mapped, clean,
    jump_run, rfl, branch_noOpportunity mapped clean jump_run⟩

private def fields (st : State) := st.opportunistic

private theorem setAlias_fields {st next : State} {dst src : Reg}
    (h : st.setAlias dst src = .ok next) : fields next = fields st := by
  cases dst <;> cases src <;>
    simp only [State.setAlias, bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at h
  all_goals repeat' first | (solve | cases h) | (solve | cases h; rfl) | split at h

private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)

private theorem binding_fields {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : fields next = fields st := by
  unfold bindResults at h
  apply fold_fields_eq (fun a : State × Array MInst => fields a.1) _ ?_ pairs h
  intro acc pair next he
  rcases acc with ⟨s, code⟩
  rcases pair with ⟨v, rs⟩
  dsimp only at he
  cases hm : ctx.valueReg? v with
  | none => simp only [hm] at he; cases he
  | some r =>
    simp only [hm] at he
    split at he
    · rename_i _ n cls
      cases ha : s.setAlias r (.vreg n cls) with
      | error e => simp only [ha, bind, Except.bind] at he; cases he
      | ok q =>
        simp only [ha, bind, Except.bind, pure, Except.pure] at he
        cases he
        exact setAlias_fields ha
    · cases he; rfl
    · cases he

/-- Actual result binding after a successful source root retains its remembered
state, including virtual aliases and physical-register result copies. -/
theorem emission_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {i : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[i]? = some info) (original : info.clif = some inst)
    {before : State} {emission : Emission}
    (run : emitInstruction ctx i before = .ok emission) :
    emission.state.opportunistic = before.opportunistic := by
  unfold emitInstruction at run
  cases lowered : Stock.runTerm ctx "lower" [.inst i] before with
  | error e => simp only [lowered, bind, Except.bind] at run; cases run
  | ok root =>
    rcases root with ⟨out, after, trace⟩
    have preserved := statement_noOpportunity mapped clean source original lowered
    simp only [lowered, bind, Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      dsimp only at run
      split at run
      · cases run
      · cases bound : bindResults ctx (ctx.insts[i]!.results.zip rss) after with
        | error e => simp only [bound, bind, Except.bind] at run; cases run
        | ok result =>
          rcases result with ⟨final, copies⟩
          simp only [bound, pure, Except.pure] at run
          cases run
          exact (binding_fields bound).trans preserved

/-- The real constant root installs an actual result alias, exercising emission
and binding rather than only an empty or omitted path. -/
theorem emission_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (info : IInfo) (emission : Emission),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      emitInstruction ctx 0 sinkState = .ok emission ∧
      (emission.state.alias[193]?).join = some 194 ∧
      emission.state.opportunistic = sinkState.opportunistic := by
  obtain ⟨f, ctx, ranges, initial, info, after, trace, scope, build, source, original,
    results, mappedReg, run⟩ := stock_statement_selectedConstant_built_witness
  have named := named_of_apply program_termByName_lower run
  have mapped := buildCtx_mappedInv scope build
  have clean := clean_stock build
  let final : State := {after with alias := aliasStep after.alias (193, 194)}
  have bound : bindResults ctx [(2, [.vreg 194 .int])] after = .ok (final, #[]) :=
    bindResults_virtual ctx after [(2, 193, 194)] (by
      intro p member; simp only [List.mem_singleton] at member; subst p; exact mappedReg)
  let emission : Emission := ⟨final, final.base.emitted, [[.vreg 194 .int]], (trace.push 582).toList⟩
  have actual : emitInstruction ctx 0 sinkState = .ok emission := by
    have infoEq : ctx.insts[0]! = info := by simp only [getElem!_def, source, Option.getD_some]
    unfold emitInstruction
    rw [infoEq, named]
    simp only [bind, Except.bind, results, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_and, Bool.false_eq_true, ite_false, List.zip_cons_cons, List.zip_nil_left,
      bound, pure, Except.pure, Array.append_empty]
    rfl
  refine ⟨f, ctx, info, emission, mapped, clean, source, original, results, mappedReg, actual, ?_,
    emission_noOpportunity mapped clean source original actual⟩
  change ((aliasStep after.alias (193, 194))[193]?).join = some 194
  rw [aliasStep_get]
  simp

end Backend.Stock.Proof.Coverage

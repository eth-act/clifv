import FV.Backend.Proof.StockSourceSinkModel
import FV.Backend.Proof.IselCovDriver

/-! Source and branch roots preserve every empty-CLIF sunk bit. The chosen
rule is classified by the same original exclusions as legacy coverage. -/
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
theorem stock_statement_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (out, after, trace))
    {terminal : Nat} (slot : ctx.insts[terminal]!.clif = none) (unsunk : before.sunk[terminal]! = false) :
    after.sunk[terminal]! = false := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := sourceSinkModel mapped clean terminal slot
  have cert := Invariant.soundAt mapped md {} sourceSinkTab rfl stock_sourceSink_table_checked
    (Config.fuel ({} : Config))
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have input := holds_inst mapped.identityView (show (sourceIdentityCtx ctx).insts[ii]? = some info from source)
    original
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle [.xv .inst] AW.top r = true ∨
        ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠
          .ok (some env, next) := by
    intro r member
    have checked := List.all_eq_true.mp stock_sourceSink_roots_checked.1 r member
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at checked
    rcases checked with excluded | checked
    · exact .inr (stock_lower_nonroot_nomatch view mapped.identityView source original member excluded)
    · exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] AW.top [.inst ii]
    before #[] out after finalTrace data_program.t686 term_686_kind rules input unsunk lowered).1

/-- Every successful actual branch root retains remembered definitions. The
same fixed branch rule checks admit its real instruction/label arguments. -/
theorem stock_branch_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {targets : List Label} {before after : State} {out : Option V}
    {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets] before =
      .ok (out, after, trace))
    {terminal : Nat} (slot : ctx.insts[terminal]!.clif = none) (unsunk : before.sunk[terminal]! = false) : after.sunk[terminal]! = false := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower_branch] at lookup
  cases lookup
  let md := sourceSinkModel mapped clean terminal slot
  have cert := Invariant.soundAt mapped md {} sourceSinkTab rfl stock_sourceSink_table_checked
    (Config.fuel ({} : Config))
  have input : Holds2 f (sourceIdentityCtx ctx) [AW.c0, AW.c0] [.inst ti, .labels targets] :=
    ⟨γ_c0_inst ti, γ_c0_labels targets, trivial⟩
  exact (cert.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [AW.c0, AW.c0]
    AW.top _ before #[] out after finalTrace data_program.t687 term_687_kind
    (fun r member => .inl (List.all_eq_true.mp stock_sourceSink_roots_checked.2.2 r member))
    input unsunk lowered).1

private theorem stock_ruleFmt_match {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447 + 36)
    {fuel ti : Nat} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st =
      .ok (some env, next)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT - 2447) fs := by
  have bound : fT - 2447 < 36 := by omega
  obtain ⟨term, lookup, kind⟩ := fmtKinds_program (fT - 2447) bound
  rw [show 2447 + (fT - 2447) = fT by omega] at lookup
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, _⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1, head, _⟩ := matchArgs_cons_inv args
      exact rootFmt_match_k data_program format lookup kind head
    · cases format

private theorem stock_lower_term_nomatch {ctx : Ctx} {ti : Nat} {t : Clif.Terminator}
    {data : V} (retTrap : retOrTrap t = true) (dataRun : Backend.termData t = .ok data)
    (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {r : Rule}
    (member : r ∈ program.rulesOf TId.lower) (notRoot : termRootRule r = false) :
    ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st ≠
      .ok (some env, next) := by
  intro fuel st env next matched
  have checked := List.all_eq_true.mp lower_fmts r member
  simp only [lowerFmtOk, notRoot, Bool.false_or] at checked
  split at checked
  · rename_i fT format
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at checked
    obtain ⟨⟨⟨lo, hi⟩, notRet⟩, notTrap⟩ := checked
    obtain ⟨info, fields, source, shape⟩ := stock_ruleFmt_match format lo hi matched
    rw [slot] at source
    cases source
    obtain ⟨fields', rfl⟩ := termData_fmt dataRun
    simp only [V.data.injEq] at shape
    cases t <;> simp [retOrTrap] at retTrap <;> simp [termFmt] at shape <;>
      first | omega | simp [Backend.termData, throw, throwThe, MonadExceptOf.throw] at dataRun
  · cases checked

theorem stock_retTrap_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ti] before = .ok (out, after, trace))
    {terminal : Nat} (emptySlot : ctx.insts[terminal]!.clif = none) (unsunk : before.sunk[terminal]! = false) :
    after.sunk[terminal]! = false := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := sourceSinkModel mapped clean terminal emptySlot
  have cert := Invariant.soundAt mapped md {} sourceSinkTab rfl stock_sourceSink_table_checked
    (Config.fuel ({} : Config))
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program sourceSinkTab aext sourceSinkActor sourceSinkPre aOracle [AW.c0] AW.top r = true ∨
        ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st ≠
          .ok (some env, next) := by
    intro r member
    cases root : termRootRule r with
    | false => exact .inr (stock_lower_term_nomatch retTrap dataRun slot member root)
    | true =>
      have checked := List.all_eq_true.mp stock_sourceSink_roots_checked.2.1 r member
      simp only [termRootRule] at root
      simp only [root, Bool.not_true, Bool.false_or] at checked
      exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [AW.c0] AW.top [.inst ti]
    before #[] out after finalTrace data_program.t686 term_686_kind rules
    ⟨γ_c0_inst ti, trivial⟩ unsunk lowered).1

private def fields (st : State) := st.sunk

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

/-- Result aliases and physical copies retain the sunk bits. -/
theorem bindResults_noSink {ctx : Ctx} {pairs : List (Nat × List Reg)}
    {st next : State} {copies : Array MInst}
    (h : bindResults ctx pairs st = .ok (next, copies)) : next.sunk = st.sunk := by
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

end Backend.Stock.Proof.Coverage

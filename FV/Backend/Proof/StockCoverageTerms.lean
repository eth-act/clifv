import FV.Backend.Proof.StockCoverageRoots

/-! Return/trap roots use the actual Stock state and existing format exclusions.
These complete the named-root prerequisites for scan and whole-driver composition. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

/-- A successful actual return/trap root retains remembered definitions. Only
its two real terminator rules can match the supplied term-data slot. -/
theorem retTrap_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ti] before = .ok (out, after, trace)) :
    after.opportunistic = before.opportunistic := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := model mapped clean before.opportunistic
  have cert := soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor noOpportunityPre aOracle [AW.c0] AW.top r = true ∨
        ∀ fuel st env next, (matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st ≠
          .ok (some env, next) := by
    intro r member
    cases root : termRootRule r with
    | false => exact .inr (stock_lower_term_nomatch retTrap dataRun slot member root)
    | true =>
      have checked := List.all_eq_true.mp stock_noOpportunity_roots_checked.2.1 r member
      simp only [termRootRule] at root
      simp only [root, Bool.not_true, Bool.false_or] at checked
      exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [AW.c0] AW.top [.inst ti]
    before #[] out after finalTrace data_program.t686 term_686_kind rules
    ⟨γ_c0_inst ti, trivial⟩ rfl lowered).1

/-- Result binding after an actual return/trap root preserves remembered definitions. -/
theorem emission_retTrap_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {i : Nat} {t : Clif.Terminator} {data : V}
    (retTrap : retOrTrap t = true) (dataRun : Backend.termData t = .ok data)
    (slot : ctx.insts[i]? = some ⟨data, [], [], none⟩)
    {before : State} {emission : Emission}
    (run : emitInstruction ctx i before = .ok emission) :
    emission.state.opportunistic = before.opportunistic := by
  unfold emitInstruction at run
  cases lowered : Stock.runTerm ctx "lower" [.inst i] before with
  | error e => simp only [lowered, bind, Except.bind] at run; cases run
  | ok root =>
    rcases root with ⟨out, after, trace⟩
    have preserved := retTrap_noOpportunity mapped clean retTrap dataRun slot lowered
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
          exact (bindResults_noOpportunity bound).trans preserved

private theorem scanState_noOpportunity (input : State) (i : Nat) :
    (scanState input i).opportunistic = input.opportunistic := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Scanning a return/trap slot preserves remembered definitions through either
an already-sunk transition or actual mandatory emission. -/
theorem scan_retTrap_noOpportunity {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {t : Clif.Terminator} {data : V}
    (retTrap : retOrTrap t = true) (dataRun : Backend.termData t = .ok data)
    (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {input : State} {output : Scan}
    (run : scanInstruction ctx block ti ti false input = .ok output) :
    output.state.opportunistic = input.opportunistic := by
  by_cases sunk : input.sunk[ti]! = true
  · simp only [scanInstruction, sunk, ite_true] at run
    cases run
    rfl
  · simp only [scanInstruction, sunk, ite_false, ite_true, beq_self_eq_true, Bool.and_false,
      Bool.false_eq_true, Bool.not_true, Bool.false_and, Bool.and_false] at run
    cases emitted : emitInstruction ctx ti (scanState input ti) with
    | error e => simp only [emitted, bind, Except.bind] at run; cases run
    | ok emission =>
      simp only [emitted, bind, Except.bind, pure, Except.pure] at run
      cases run
      exact (emission_retTrap_noOpportunity mapped clean retTrap dataRun slot emitted).trans
        (scanState_noOpportunity input ti)

private def returnFunction : Clif.Function := {
  name := "stock_return_preservation"
  sig := {callConv := some .systemV}
  blocks := [{id := 0, term := .ret []}] }
private def returnBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx returnFunction).toOption.getD (sinkCtx, #[], sinkState)
private def returnData : V := (Backend.termData (.ret [])).toOption.getD (.op .unit)
private def returnCtx : Ctx := Driver.termCtx returnBuilt.1 0 returnData
private def returnAfter : State :=
  {returnBuilt.2.2 with base := returnBuilt.2.2.base.emit (.rets [])}
private theorem return_build : Stock.buildCtx returnFunction = .ok returnBuilt := rfl
private theorem return_scope : LowerScope returnFunction := lowerScope_of (by decide +kernel)
private theorem return_run : Stock.runTerm returnCtx "lower" [.inst 0] returnBuilt.2.2 =
    .ok (some (.regsVec []), returnAfter, [77, 1037]) := by rfl

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

/-- A nonempty real function emits an actual return chunk through the term-data
slot, inhabiting the return/trap root and context premises. -/
theorem retTrap_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial after : State) (data : V),
      LowerScope f ∧ f.blocks.length = 1 ∧ MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      Backend.termData (.ret []) = .ok data ∧ ctx.insts[0]? = some ⟨data, [], [], none⟩ ∧
      Stock.runTerm ctx "lower" [.inst 0] initial = .ok (some (.regsVec []), after, [77, 1037]) ∧
      after.base.emitted = #[.rets []] ∧ after.opportunistic = initial.opportunistic := by
  have mapped : MappedCtxInv returnFunction returnCtx :=
    (buildCtx_mappedInv return_scope return_build).termCtx (by rfl) returnData
  have data : Backend.termData (.ret []) = .ok returnData := rfl
  have clean : Clean (sourceIdentityCtx returnCtx) := clean_termCtx (clean_stock return_build) data 0
  exact ⟨returnFunction, returnCtx, returnBuilt.2.2, returnAfter, returnData,
    return_scope, rfl, mapped, clean, data, rfl, return_run, rfl,
    retTrap_noOpportunity mapped clean rfl data rfl return_run⟩

/-- Actual return emission, including its result binder, inhabits the emission theorem. -/
theorem emission_retTrap_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial : State) (emission : Emission) (data : V),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      Backend.termData (.ret []) = .ok data ∧ ctx.insts[0]? = some ⟨data, [], [], none⟩ ∧
      emitInstruction ctx 0 initial = .ok emission ∧ emission.code = #[.rets []] ∧
      emission.state.opportunistic = initial.opportunistic := by
  have mapped : MappedCtxInv returnFunction returnCtx :=
    (buildCtx_mappedInv return_scope return_build).termCtx (by rfl) returnData
  have data : Backend.termData (.ret []) = .ok returnData := rfl
  have clean := clean_termCtx (clean_stock return_build) data 0
  let emission : Emission := ⟨returnAfter, #[.rets []], [], [77, 1037]⟩
  have run : emitInstruction returnCtx 0 returnBuilt.2.2 = .ok emission := rfl
  exact ⟨returnFunction, returnCtx, returnBuilt.2.2, emission, returnData, mapped, clean,
    data, rfl, run, rfl, emission_retTrap_noOpportunity mapped clean rfl data rfl run⟩

/-- The mandatory return scan emits a real return, rather than skipping the slot. -/
theorem scan_retTrap_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (initial : State) (output : Scan) (data : V),
      MappedCtxInv f ctx ∧ Clean (sourceIdentityCtx ctx) ∧
      Backend.termData (.ret []) = .ok data ∧ ctx.insts[0]? = some ⟨data, [], [], none⟩ ∧
      scanInstruction ctx 0 0 0 false initial = .ok output ∧ output.emitted = #[.rets []] ∧
      output.state.opportunistic = initial.opportunistic := by
  have mapped : MappedCtxInv returnFunction returnCtx :=
    (buildCtx_mappedInv return_scope return_build).termCtx (by rfl) returnData
  have data : Backend.termData (.ret []) = .ok returnData := rfl
  have clean := clean_termCtx (clean_stock return_build) data 0
  let before := scanState returnBuilt.2.2 0
  let after : State := {before with base := before.base.emit (.rets [])}
  let emission : Emission := ⟨after, #[.rets []], [], [77, 1037]⟩
  let output : Scan := emission.scan 0 0 before
  have run : scanInstruction returnCtx 0 0 0 false returnBuilt.2.2 = .ok output := rfl
  exact ⟨returnFunction, returnCtx, returnBuilt.2.2, output, returnData, mapped, clean,
    data, rfl, run, rfl, scan_retTrap_noOpportunity mapped clean rfl data rfl run⟩

end Backend.Stock.Proof.Coverage

import FV.Backend.Proof.StockBindingCoverage
import FV.Backend.Proof.StockCoverageBlock

namespace Backend.Stock.Proof.Coverage.TerminalDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

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

theorem stock_retTrap_emission_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ti] before = .ok (out, after, trace)) :
    CovSince before.base after.base := by
  obtain ⟨term, finalTrace, lookup, lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := Emission.model mapped clean before.base
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
    ⟨γ_c0_inst ti, trivial⟩ (covSince_refl _) lowered).1


theorem stock_emit_retTrap_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    {before : State} {emission : Emission} (empty : before.base.emitted = #[])
    (run : emitInstruction ctx ti before = .ok emission) :
    ∀ i ∈ emission.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold emitInstruction at run
  have atInfo : ctx.insts[ti]! = ⟨data,[],[],none⟩ := by rw [getElem!_def,slot]
  cases lowered : Stock.runTerm ctx "lower" [.inst ti] before with
  | error e => simp only [lowered,bind,Except.bind] at run; cases run
  | ok answer =>
    rcases answer with ⟨out,next,trace⟩
    simp only [lowered,bind,Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      dsimp only at run
      rw [atInfo] at run
      simp only [List.isEmpty_nil,Bool.not_true,Bool.and_false,ite_false,List.zip_nil_left,
        bindResults,List.foldlM_nil,pure,Except.pure,bind,Except.bind] at run
      cases run
      obtain ⟨code,since,covered⟩ := stock_retTrap_emission_coverage mapped clean retTrap dataRun slot lowered
      intro i member
      dsimp only at member
      rw [Array.append_empty,since,empty,Array.empty_append] at member
      have form := covered i (by simpa only [List.toList_toArray] using member)
      refine ⟨form,fun ordinary => spillInstOk_of_formOk (ctx := default) ?_⟩
      simpa only [Covered,ordinary,Bool.false_or] using form

theorem stock_scan_retTrap_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ii]? = some ⟨data,[],[],none⟩)
    {input : State} {output : Scan}
    (run : scanInstruction ctx block ii ti branch input = .ok output) :
    ∀ i ∈ output.emitted.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold scanInstruction at run
  dsimp only at run
  repeat' first
    | (solve | cases run; intro i member; cases member)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals first
    | (solve | cases run)
    | (cases run
       exact stock_emit_retTrap_form_coverage mapped clean retTrap dataRun slot
         (before := scanState input ii)
         (by unfold scanState; dsimp only; split <;> rfl) (by assumption))

theorem stock_scan_slot_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} (slot : ScanSlot ctx ii ti branch)
    {input : State} {output : Scan}
    (run : scanInstruction ctx block ii ti branch input = .ok output) :
    ∀ i ∈ output.emitted.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  rcases slot with ⟨info,inst,source,original⟩ | branchSlot | ⟨term,data,retTrap,prepared,source⟩
  · exact Result.stock_scanInstruction_form_coverage mapped clean source original run
  · obtain ⟨equal,isBranch⟩ := branchSlot
    subst ii
    subst branch
    by_cases sunk : input.sunk[ti]! = true
    · simp only [scanInstruction,sunk,ite_true] at run
      cases run
      intro i member
      cases member
    · simp only [scanInstruction,sunk,ite_false,beq_self_eq_true,Bool.true_and,ite_true] at run
      cases run
      intro i member
      cases member
  · exact stock_scan_retTrap_form_coverage mapped clean retTrap prepared source run


theorem stock_scanBlock_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {branch : Bool} {indices : List Nat}
    (slots : ∀ i ∈ indices,ScanSlot ctx i ti branch)
    {input : State} {output : BlockScan}
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    ∀ i ∈ output.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => intro i member; cases member
  | @cons ii indices input scan tail head rest ih =>
    intro i member
    have either : i ∈ tail.code.toList ∨ i ∈ scan.emitted.toList := by
      simpa only [Array.toList_append,List.mem_append] using member
    rcases either with left | right
    · exact ih (fun j member => slots j (List.mem_cons_of_mem ii member)) i left
    · exact stock_scan_slot_form_coverage mapped clean (slots ii (List.mem_cons_self ..)) head i right

private theorem placeholder {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ctx.insts[blockStart f bi + b.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  rw [view.insts]
  exact spec.facts.term bi b block

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem clean_block {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {t : Clif.Terminator} {data : V}
    (prepared : blockData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases t <;> simp only [blockData] at prepared
  all_goals first
    | exact clean_tryCtx clean prepared ti trs
    | exact clean_termCtx clean prepared ti

theorem stock_built_scanBlock_form_coverage {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data) (trs : List Reg × List Reg)
    {input : State} {output : BlockScan}
    (run : scanBlock {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs}
      bi (range.2 - 1) (blockBranch b.term)
      (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList) input = .ok output) :
    ∀ i ∈ output.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : range.2 - 1 = blockStart f bi + b.body.length := by cases rangeEq; omega
  have ph : ctx.insts[range.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]
    exact placeholder build block
  have mapped := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs trs
  exact stock_scanBlock_form_coverage mapped (clean_block (clean_stock build) prepared _ trs)
    (built_scan_slots build scope block rangeRun prepared trs) run




end Backend.Stock.Proof.Coverage.TerminalDraft

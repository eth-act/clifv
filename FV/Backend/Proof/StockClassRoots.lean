import FV.Backend.Proof.StockClassModel
import FV.Backend.Proof.StockInitialClasses
import FV.Backend.Proof.StockCoverageTerms
namespace Backend.Stock.Proof.OperandClassDraft
open Backend.Proof Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Successful actual context construction supplies the entire initial class
invariant, including the context's original empty try-register lists. -/
theorem stock_build_initial_classInvariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,st)) : ClsIs ctx st.base st.base := by
  obtain ⟨size,values,reserved⟩ := InitialClassesDraft.stock_build_classes build
  obtain ⟨original,old,requests,legacy,_,same⟩ := buildCtx_allocation build
  have context := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.1.tryRegs) same
  change ctx.tryRegs = original.tryRegs at context
  rw [(ctxSpec_of legacy).facts.tryRegs] at context
  refine ⟨size,values,?_,?_,⟨[],by simp,by simp⟩⟩
  · intro r member; rw [context] at member; cases member
  · intro r member; rw [context] at member; cases member

/-- Actual reserved registers supply the term-context class invariant, including
an absent reservation slot, whose register lists are empty. -/
theorem stock_build_term_classInvariant {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,st)) (ti : Nat) (data : V) :
    ClsIs {Driver.termCtx ctx ti data with tryRegs := st.tryRegs[ti]!} st.base st.base := by
  obtain ⟨size,values,reserved⟩ := InitialClassesDraft.stock_build_classes build
  have lists : ∀ r ∈ st.tryRegs[ti]!.1 ++ st.tryRegs[ti]!.2,RegCls st.base.classes r := by
    intro r member
    cases found : st.tryRegs[ti]? with
    | none => simp only [getElem!_def,found,Option.getD_none] at member; cases member
    | some rs =>
      simp only [getElem!_def,found,Option.getD_some] at member
      exact reserved ti rs found r member
  exact ⟨size,values,fun r member => lists r (List.mem_append_left _ member),
    fun r member => lists r (List.mem_append_right _ member),⟨[],by simp,by simp⟩⟩

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

private theorem stock_rootOp_match {ctx : Ctx} {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT))
    {tf to : Term} {kf o : Nat} (htf : termOf program fT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf program oT = .ok to) (hko : to.kind = .enumVariant o) {m ii : Nat} {vs : List V}
    {s s1 : State × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (Stock.sem ctx) {} m r (.inst ii :: vs)).run s = .ok (some env, s1)) :
    ∃ info fs, ctx.insts[ii]? = some info ∧ info.data = .data 152 kf (.data 151 o [] :: fs) := by
  cases m with
  | zero => rw [matchRule.eq_1] at h; cases h
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
    rw [stock_matchArgs] at ha
    unfold rootOp at hq
    split at hq
    · rename_i q1 fT' oT' rest qs hargs
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl h1
      rw [Backend.Proof.sem_extract] at hx
      obtain ⟨info, hinfo, rfl⟩ := ext_inst_data_value_inv hx
      obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
      obtain ⟨e3, hp2, -⟩ := matchArgs_cons_inv hm2
      obtain ⟨fs', hu, hm3⟩ := matchPat_enum_inv htf hkf hp2
      have hd := sem_unData_inv hu
      cases fs' with
      | nil =>
        rw [matchArgs.eq_3] at hm3
        all_goals first | cases hm3 | (intros; simp_all)
      | cons g gs =>
        obtain ⟨e4, hp3, -⟩ := matchArgs_cons_inv hm3
        obtain ⟨fs1, hu1, hm4⟩ := matchPat_enum_inv hto hko hp3
        have hg := sem_unData_inv hu1
        cases fs1 with
        | nil => exact ⟨info, gs, hinfo, by rw [hd, hg]⟩
        | cons _ _ =>
          rw [matchArgs.eq_3] at hm4
          all_goals first | cases hm4 | (intros; simp_all)
    · cases hq

private theorem stock_pinned_names {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT)) {kf o : Nat}
    (hk : (match termOf program fT with | .ok t => t.kind == .enumVariant kf | .error _ => false) = true)
    (ho : (match termOf program oT with | .ok t => t.kind == .enumVariant o | .error _ => false) = true)
    {m : Nat} {s s1 : State × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (Stock.sem ctx) {} m r [.inst ii]).run s = .ok (some env, s1)) :
    (variantNames 151)[o]? = some (instNames inst).2 := by
  obtain ⟨tf, htf, hkf⟩ := kind_of hk
  obtain ⟨to, hto, hko⟩ := kind_of ho
  obtain ⟨info', fs, hi', hd⟩ := stock_rootOp_match hq htf hkf hto hko h
  rw [hi] at hi'; cases hi'
  have := hctx.data ii info inst hi hc
  rw [hd] at this
  exact (instData_inv_names this).2


private theorem holds_inst_classes (s : State) (i : Nat) :
    Holds2 (fun a s v => γC a s.base v) s [⟨1,true⟩] [.inst i] :=
  ⟨fun _ r hr => by simp [V.regsIn] at hr,trivial⟩

/-- Actual mapped source-statement lowering derives emitted operand classes
and nonempty-result class meaning from the unchanged fixed class analysis. -/
theorem stock_statement_classes {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx) (hcl : Cov.Clean ctx)
    {ii : Nat} {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {s : State} {out : Option V} {s' : State} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) (hIs : ClsIs ctx s.base s.base) :
    ClsIs ctx s.base s'.base ∧ ∀ v, out = some v → info.results ≠ [] → GoodV s'.base.classes v := by
  obtain ⟨t, tr', ht, happ⟩ := named_run_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have sa := soundAtC (md := stock_class_model hcl s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
  have hrulesTop : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] FA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (Stock.sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hf
    rcases hf with hcr | ⟨ha, -⟩
    · exact .inr (stock_lower_nonroot_nomatch (show DFGViewEq ctx (sourceIdentityCtx ctx) from ⟨rfl,rfl,rfl,rfl,rfl⟩) hctx.identityView hi hc hrl hcr)
    · exact .inl ha
  refine ⟨(sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] FA.top [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrulesTop (holds_inst_classes s ii) hIs happ).1, ?_⟩
  intro v hout hres
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (Stock.sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp clsRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [clsRootOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at hf
    rcases hf with hcr | ⟨-, h587 | ha⟩
    · exact .inr (stock_lower_nonroot_nomatch (show DFGViewEq ctx (sourceIdentityCtx ctx) from ⟨rfl,rfl,rfl,rfl,rfl⟩) hctx.identityView hi hc hrl hcr)
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := stock_pinned_names hctx hi hc hop.1 kind_nullAry kind_nop hm
      rw [variantNames_Nop] at hn
      have hnop := instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  exact (sa.root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩ [.inst ii] s #[] out s'
    tr' data_program.t686 term_686_kind hrules (holds_inst_classes s ii) hIs happ).2 v hout (by decide)


/-- Every actual branch root, including calls, preserves complete emitted
register-class consistency under the existing class invariant. -/
theorem stock_branch_classes {ctx : Ctx} (hcl : Cov.Clean ctx) {ti : Nat} {targets : List Label} {s : State}
    {out : Option V} {s' : State} {tr : List Isle.RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr))
    (hIs : ClsIs ctx s.base s.base) : ClsIs ctx s.base s'.base := by
  obtain ⟨t, tr', ht, happ⟩ := named_run_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have sa := soundAtC (md := stock_class_model hcl s) (cfg := {}) (tab := clsTab) rfl clsTab_ok 1000000
  have hins : Holds2 (fun a s v => γC a s.base v) s [⟨1, true⟩, FA.c0] [.inst ti, .labels targets] :=
    ⟨fun _ r hr => by simp [V.regsIn] at hr, fun _ r hr => by simp [V.regsIn] at hr, trivial⟩
  exact (sa.root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _ [⟨1, true⟩, FA.c0] FA.top _ s
    #[] out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp clsBranch_ok rl hrl)) hins hIs happ).1


/-- Actual return/trap roots use the same class analysis; source term data
internally excludes every other root format. -/
theorem stock_retTrap_classes {ctx : Ctx} (clean : Clean ctx)
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    {before after : State} {out : Option V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ti] before = .ok (out,after,trace))
    (invariant : ClsIs ctx before.base before.base) : ClsIs ctx before.base after.base := by
  obtain ⟨term,finalTrace,lookup,lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let model := stock_class_model clean before
  have cert := soundAtC (md := model) (cfg := {}) (tab := clsTab) rfl clsTab_ok (Config.fuel ({} : Config))
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRuleC program clsTab false [⟨1,true⟩] FA.top r = true ∨
        ∀ fuel st env next,(matchRule program (Stock.sem ctx) {} fuel r [.inst ti]).run st ≠ .ok (some env,next) := by
    intro r member
    cases root : termRootRule r with
    | false => exact .inr (stock_lower_term_nomatch retTrap dataRun slot member root)
    | true =>
      have checked := List.all_eq_true.mp clsTerm_ok r member
      simp only [root,Bool.not_true,Bool.false_or] at checked
      exact .inl checked
  exact (cert.root T.lower.ret T.lower.id T.lower _ _ [⟨1,true⟩] FA.top [.inst ti]
    before #[] out after finalTrace data_program.t686 term_686_kind rules
    (holds_inst_classes before ti) invariant lowered).1

end Backend.Stock.Proof.OperandClassDraft

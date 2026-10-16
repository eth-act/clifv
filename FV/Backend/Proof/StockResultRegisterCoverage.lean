import FV.Backend.Proof.StockResultRegisterTable

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program

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

private theorem stock_rootOp_match {ctx original : Ctx} (view : DFGViewEq ctx original) {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT))
    {tf to : Term} {kf o : Nat} (htf : termOf program fT = .ok tf) (hkf : tf.kind = .enumVariant kf)
    (hto : termOf program oT = .ok to) (hko : to.kind = .enumVariant o) {m ii : Nat} {vs : List V}
    {s s1 : State × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (Stock.sem ctx) {} m r (.inst ii :: vs)).run s = .ok (some env, s1)) :
    ∃ info fs, original.insts[ii]? = some info ∧ info.data = .data 152 kf (.data 151 o [] :: fs) := by
  cases m with
  | zero => rw [matchRule.eq_1] at h; cases h
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv h
    rw [stock_matchArgs_source view] at ha
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

private theorem stock_pinned_names {f : Clif.Function} {ctx original : Ctx}
    (view : DFGViewEq ctx original) (hctx : CtxInv f original) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : original.insts[ii]? = some info)
    (hc : info.clif = some inst) {r : Rule} {fT oT : Nat}
    (hq : rootOp r = some (fT, oT)) {kf o : Nat}
    (hk : (match termOf program fT with | .ok t => t.kind == .enumVariant kf | .error _ => false) = true)
    (ho : (match termOf program oT with | .ok t => t.kind == .enumVariant o | .error _ => false) = true)
    {m : Nat} {s s1 : State × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (Stock.sem ctx) {} m r [.inst ii]).run s = .ok (some env, s1)) :
    (variantNames 151)[o]? = some (instNames inst).2 := by
  obtain ⟨tf, htf, hkf⟩ := kind_of hk
  obtain ⟨to, hto, hko⟩ := kind_of ho
  obtain ⟨info', fs, hi', hd⟩ := stock_rootOp_match view hq htf hkf hto hko h
  rw [hi] at hi'; cases hi'
  have := hctx.data ii info inst hi hc
  rw [hd] at this
  exact (instData_inv_names this).2

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



/-- Actual Stock source statements with results return only integer virtual
registers. The unchanged source invariant and a kernel-checked result summary
derive this internally, including failed matches and exception contexts. -/
theorem stock_statement_result_registers {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before after : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower" [.inst ii] before = .ok (some out,after,trace))
    (nonempty : info.results ≠ []) :
    ∀ r ∈ out.regsIn,∃ n,r = .vreg n .int := by
  obtain ⟨term,finalTrace,lookup,lowered⟩ := named_run_apply run
  rw [program_termByName_lower] at lookup
  cases lookup
  let md := Emission.model mapped clean before.base
  have cert := Coverage.soundAt mapped md {} covTab rfl stock_noOpportunity_table_checked
    (Config.fuel ({} : Config))
  have input := holds_inst mapped.identityView (show (sourceIdentityCtx ctx).insts[ii]? = some info from source) original
  have view : DFGViewEq ctx (sourceIdentityCtx ctx) := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have rules : ∀ r ∈ program.rulesOf T.lower.id,
      aRule program covTab aext actor noOpportunityPre aOracle [.xv .inst] (.flat 1 true) r = true ∨
        ∀ fuel st env next,(matchRule program (Stock.sem ctx) {} fuel r [.inst ii]).run st ≠ .ok (some env,next) := by
    intro r member
    have checked := List.all_eq_true.mp stock_statement_result_table_checked r member
    have op := List.all_eq_true.mp lower_ops r member
    simp only [Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq] at checked
    rcases checked with (excluded | nop) | checked
    · exact .inr (stock_lower_nonroot_nomatch view mapped.identityView source original member excluded)
    · refine .inr fun fuel st env next matched => nonempty ?_
      simp only [nop,bne_self_eq_false,Bool.false_or,Bool.and_eq_true,beq_iff_eq] at op
      have name := stock_pinned_names view mapped.identityView source original op.1 kind_nullAry kind_nop matched
      rw [variantNames_Nop] at name
      have isNop := instNames_nop (Option.some.inj name).symm
      subst inst
      obtain ⟨types,typed,_,length⟩ := mapped.identityView.resTys ii info .nop source original
      simp [Clif.Inst.resultTypes] at typed
      subst types
      exact List.eq_nil_of_length_eq_zero length
    · exact .inl checked
  obtain ⟨_,value⟩ := cert.root T.lower.ret T.lower.id T.lower _ _ [.xv .inst] (.flat 1 true) [.inst ii]
    before #[] (some out) after finalTrace data_program.t686 term_686_kind rules input (covSince_refl _) lowered
  intro r member
  have kind := (value _ rfl).1 r member
  rcases kind_cases r with same | same | same | same
  · exact kind_int same
  all_goals rw [same] at kind; exact (kind (by decide)).elim

end Backend.Stock.Proof.Coverage.Result

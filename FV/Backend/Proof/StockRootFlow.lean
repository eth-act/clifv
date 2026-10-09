import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.StockPatternSource
import FV.Backend.Proof.StockMappedFlow
import FV.Backend.Proof.StockConstantRoot
import FV.Backend.Proof.IselFlow

namespace Backend.Stock.Proof.MappedFlow
attribute [local irreducible] Isle.Aarch64.program
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

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
      rw [sem_extract] at hx
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

/-- Actual stock root execution in a validated mapped source context returns
either a fresh register or a mapped operand-provenance register. This also
applies to validated terminator-overridden contexts with no exception reservations;
the canonical identity context is only a proof view for pure source matching. -/
theorem stock_root_mapped_context_flow {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (empty : ctx.tryRegs = ([], []))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (run : (applyTerm program (Stock.sem ctx) {} fuel T.lower.ret T.lower.id [.inst ii]).run
      (before, trace) = .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg o cls) := by
  intro rss hout hres rs hrs o cls hrso
  let original := sourceIdentityCtx ctx
  have view : DFGViewEq ctx original := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hctx : CtxInv f original := mapped.identityView
  have hi0 : original.insts[ii]? = some info := by simpa only [view.insts] using hi
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program flowTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (Stock.sem ctx) {} m rl [.inst ii]).run s0 ≠
          .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp flowRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [flowRootOk, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (hcr | h587) | ha
    · exact .inr (stock_lower_nonroot_nomatch view hctx hi0 hc hrl hcr)
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := stock_pinned_names view hctx hi0 hc hop.1 kind_nullAry kind_nop hm
      rw [variantNames_Nop] at hn
      have hnop := instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, _, hlen⟩ := hctx.resTys ii info .nop hi0 hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  have hins : Holds2 (γF ctx ii before.base.nextVreg) before [⟨1, true⟩] [.inst ii] := by
    refine ⟨⟨?_, ?_⟩, trivial⟩
    · intro h; cases h
    · intro _
      exact ⟨fun r hr => by simp [V.regsIn] at hr,
        fun n hn => by simp [V.valsIn] at hn,
        fun j hj => .inl ⟨rfl, by simpa [V.instsIn] using hj⟩⟩
  obtain ⟨_, hv⟩ := (soundAt (flowModel mapped hi hc empty) (cfg := {}) rfl
    flowTab_ok fuel).root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩
      [.inst ii] before trace (some out) after finalTrace data_program.t686 term_686_kind
      hrules hins (Nat.le_refl _) run
  have hcl := (hv out rfl).2 rfl
  subst hout
  exact hcl.1 (.vreg o cls) (mem_regsVec hrs (by rw [hrso]; exact List.mem_singleton_self _)) o cls rfl

/-- Successful source context construction supplies the mapped context facts
required by whole-root flow. The runtime register mapping remains dense. -/
theorem stock_root_mapped_flow {f : Clif.Function} (scope : LowerScope f)
    {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {fuel : Nat} {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (run : (applyTerm program (Stock.sem ctx) {} fuel T.lower.ret T.lower.id [.inst ii]).run
      (before, trace) = .ok (some out, (after, finalTrace))) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls,
      rs = [.vreg o cls] →
      (before.base.nextVreg ≤ o ∧ o < after.base.nextVreg) ∨
        ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg o cls) := by
  have empty : ctx.tryRegs = ([], []) := by
    obtain ⟨old, oldState, requests, hb, _, he⟩ := buildCtx_allocation built
    have h := congrArg (fun q => q.1) he
    dsimp only at h
    rw [h]
    exact (ctxSpec_of hb).facts.tryRegs
  exact stock_root_mapped_context_flow (buildCtx_mappedInv scope built) empty hi hc run

/-- The actual generated constant root allocates194 in a successfully built
context whose source result2 maps to193. The root flow theorem certifies its
fresh output without an identity source/register assumption. -/
theorem stock_root_mapped_flow_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (info : IInfo) (next : State) (trace : Array RuleId),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (sinkState, #[]) = .ok (some (.regsVec [[.vreg 194 .int]]), next, trace.push 582) ∧
      ((sinkState.base.nextVreg ≤ 194 ∧ 194 < next.base.nextVreg) ∨
        ∃ x, Prov ctx 0 x ∧ ctx.valueReg? x = some (.vreg 194 .int)) := by
  obtain ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, run⟩ :=
    stock_statement_selectedConstant_built_witness
  refine ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, run, ?_⟩
  exact stock_root_mapped_flow scope built hi hc run _ rfl
    (by rw [results]; simp) _ (List.mem_singleton_self _) _ _ rfl

theorem stock_root_mapped_context_flow_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (info : IInfo) (next : State) (trace : Array RuleId),
      LowerScope f ∧ Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      ctx.insts[0]? = some info ∧ info.clif = some (.iconst .i8 9) ∧
      info.results = [2] ∧ ctx.valueReg? 2 = some (.vreg 193 .int) ∧
      (applyTerm program (Stock.sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst 0]).run
        (sinkState, #[]) = .ok (some (.regsVec [[.vreg 194 .int]]), next, trace.push 582) ∧
      ((sinkState.base.nextVreg ≤ 194 ∧ 194 < next.base.nextVreg) ∨
        ∃ x, Prov ctx 0 x ∧ ctx.valueReg? x = some (.vreg 194 .int)) := by
  obtain ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, run⟩ :=
    stock_statement_selectedConstant_built_witness
  refine ⟨f, ctx, ranges, initial, info, next, trace, scope, built, hi, hc, results, mapped, run, ?_⟩
  exact stock_root_mapped_context_flow (buildCtx_mappedInv scope built) (by
    obtain ⟨original, st0, requests, old, _, he⟩ := buildCtx_allocation built
    have h := congrArg (fun q => q.1) he
    dsimp only at h
    rw [h]
    exact (ctxSpec_of old).facts.tryRegs) hi hc run _ rfl
    (by rw [results]; simp) _ (List.mem_singleton_self _) _ _ rfl

end Backend.Stock.Proof.MappedFlow

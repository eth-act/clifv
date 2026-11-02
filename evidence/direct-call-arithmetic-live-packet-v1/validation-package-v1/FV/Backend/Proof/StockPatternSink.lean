import FV.Backend.Proof.StockSinkProvenance
import FV.Backend.Proof.StockPatternBindings

/-! Load-pattern sink helpers obtain their instruction targets from actual
installed instruction data. These facts exclude trap terminator slots; they do
not yet establish the full evaluator's sunk-bit preservation invariant. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
attribute [local irreducible] Isle.Aarch64.program

private theorem installed_extract_inv {ctx : Ctx} {ii : Nat} {st : LState} {fs : List V}
    (h : Backend.externExtract ctx T.inst_data_value (.inst ii) st = .ok fs) :
    ∃ info, ctx.insts[ii]? = some info ∧
      fs = [.ty (info.resTys.head?.getD .invalid), info.data] := by
  change (match ctx.insts[ii]? with
    | some info => ExtResult.ok [.ty (info.resTys.head?.getD .invalid), info.data]
    | none => ExtResult.unmodeled s!"inst {ii}") = ExtResult.ok fs at h
  cases hi : ctx.insts[ii]? with
  | none => rw [hi] at h; cases h
  | some info => rw [hi] at h; cases h; exact ⟨info, rfl, rfl⟩

private theorem installed_format {ctx : Ctx} {st : State} {ii b ft fmt : Nat}
    {rest : List Pattern} {env bound : Isle.Interp.Env V} {term : Term}
    (ht : termOf program ft = .ok term) (hk : term.kind = .enumVariant fmt)
    (h : matchPat program (Stock.sem ctx) st
      (.bind 18 b (.term 18 209 [.wildcard 14, .term 152 ft rest]))
      (.inst ii) env = .ok (some bound)) :
    ∃ info fields, ctx.insts[ii]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (fmt, fields) := by
  obtain ⟨_, h⟩ := matchPat_bind_inv h
  obtain ⟨values, hx, ha⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl h
  change Backend.externExtract ctx T.inst_data_value (.inst ii) st.base = .ok values at hx
  obtain ⟨info, hi, rfl⟩ := installed_extract_inv hx
  obtain ⟨env1, _, ha⟩ := matchArgs_cons_inv ha
  obtain ⟨env2, hp, _⟩ := matchArgs_cons_inv ha
  obtain ⟨fields, hu, _⟩ := matchPat_enum_inv ht hk hp
  exact ⟨info, fields, hi, hu⟩

/-- Successful actual matching of either pattern-based sink helper requires
installed ordinary-load (16) or atomic-load (17) data at its instruction input. -/
theorem stock_loadSink_pattern {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {ii n : Nat} {ty : CTy}
    (atomic : Bool)
    (hm : (matchRule program (Stock.sem ctx) {} (n + 1)
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst ii] else [.ty ty, .inst ii])).run (st, tr) =
        .ok (some bound, matched, tr')) :
    ∃ info fields, ctx.insts[ii]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (if atomic then 17 else 16, fields) := by
  obtain ⟨env, ha, _⟩ := matchRule_some_inv hm
  cases atomic with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rule_inst_4203] at ha
    obtain ⟨env1, _, ha⟩ := matchArgs_cons_inv ha
    obtain ⟨env2, hp, _⟩ := matchArgs_cons_inv ha
    exact installed_format data_program.t2463 rfl hp
  | true =>
    simp only [↓reduceIte, rule_inst_3905] at ha
    obtain ⟨env1, hp, _⟩ := matchArgs_cons_inv ha
    exact installed_format data_program.t2464 rfl hp

private theorem noIflet_match {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {n : Nat} {r : Rule} {vs : List V}
    (hil : r.iflets = [])
    (hm : (matchRule program (Stock.sem ctx) {} (n + 1) r vs).run (st, tr) =
        .ok (some bound, matched, tr')) :
    matched = st ∧ tr' = tr ∧
      matchArgs program (Stock.sem ctx) st r.args vs
        (Array.replicate r.vars.length none) = .ok (some bound) := by
  obtain ⟨env, ha, hi⟩ := matchRule_some_inv hm
  rw [hil] at hi
  cases n with
  | zero => rw [matchIfLets.eq_1] at hi; cases hi
  | succ n =>
    rw [matchIfLets.eq_2] at hi
    cases hi
    exact ⟨rfl, rfl, ha⟩

/-- Complete matching binds the sink target to its actual instruction input
and retains the original state/trace; inner address/offset bindings cannot
replace that instruction variable. -/
theorem stock_loadSink_binding {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {ii n : Nat} {ty : CTy}
    (atomic : Bool)
    (hm : (matchRule program (Stock.sem ctx) {} (n + 1)
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst ii] else [.ty ty, .inst ii])).run (st, tr) =
        .ok (some bound, matched, tr')) :
    matched = st ∧ tr' = tr ∧ bound[if atomic then 1 else 3]? = some (some (.inst ii)) := by
  obtain ⟨hs, ht, ha⟩ := noIflet_match (by cases atomic <;> rfl) hm
  refine ⟨hs, ht, ?_⟩
  cases atomic with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rule_inst_4203] at ha
    obtain ⟨env1, hp, ha⟩ := matchArgs_cons_inv ha
    obtain ⟨_, hp⟩ := matchPat_bind_inv hp
    simp only [matchPat, pure, Except.pure] at hp
    cases hp
    obtain ⟨env2, hp, ht⟩ := matchArgs_cons_inv ha
    simp only [matchArgs, pure, Except.pure] at ht
    cases ht
    obtain ⟨_, hp⟩ := matchPat_bind_inv hp
    have h := stock_pattern_keeps (k := 3) (by decide) hp
    exact h.trans (by rfl)
  | true =>
    simp only [↓reduceIte, rule_inst_3905] at ha
    obtain ⟨env1, hp, ht⟩ := matchArgs_cons_inv ha
    simp only [matchArgs, pure, Except.pure] at ht
    cases ht
    obtain ⟨_, hp⟩ := matchPat_bind_inv hp
    have h := stock_pattern_keeps (k := 1) (by decide) hp
    exact h.trans (by rfl)

private theorem rhs_sink_receipt {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env : Isle.Interp.Env V} {m j k ty : Nat} {body : Expr} {out : V}
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 5)
      (.let ty [(j, 13, .term 13 236 [.var 18 k])] body) env).run (st, tr) =
        .ok (some out, next, tr')) :
    ∃ unit sunk trace,
      (evalExpr program (Stock.sem ctx) {} (m + 3)
        (.term 13 236 [.var 18 k]) env).run (st, tr) =
          .ok (some unit, sunk, trace) := by
  rw [evalExpr.eq_6, evalBinds.eq_3] at hs
  simp only [isel_monad] at hs
  cases he : (evalExpr program (Stock.sem ctx) {} (m + 3)
      (.term 13 236 [.var 18 k]) env).run (st, tr) with
  | error e => rw [he] at hs; cases hs
  | ok pair =>
    obtain ⟨value, state⟩ := pair
    cases value with
    | none => rw [he] at hs; simp only [isel_monad] at hs; cases hs
    | some unit => exact ⟨unit, state.1, state.2, rfl⟩

private theorem sink_call_receipt {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env : Isle.Interp.Env V} {m k ii : Nat} {out : V}
    (hk : env[k]? = some (some (.inst ii)))
    (he : (evalExpr program (Stock.sem ctx) {} (m + 3)
      (.term 13 236 [.var 18 k]) env).run (st, tr) = .ok (some out, next, tr')) :
    Stock.externCtor ctx T.sink_inst [.inst ii] st = .ok (.op .unit, next) := by
  simp only [evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2, evalArgs.eq_2,
    hk, isel_monad, applyTerm.eq_2, data_program.t236, T.sink_inst, Stock.sem] at he
  cases hc : Stock.externCtor ctx T.sink_inst [.inst ii] st with
  | fail => simp only [T.sink_inst] at hc; rw [hc] at he; simp only [isel_monad] at he; cases he
  | unmodeled e => simp only [T.sink_inst] at hc; rw [hc] at he; simp only [isel_monad] at he; cases he
  | ok pair =>
    obtain ⟨value, final⟩ := pair
    have hunit := (sink_accepted hc).2.2.2.1
    subst value
    have hc' := hc
    simp only [T.sink_inst] at hc'
    rw [hc'] at he
    simp only [isel_monad, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at he
    obtain ⟨_, hn, _⟩ := he
    subst next
    rfl

/-- Successful complete match and full RHS evaluation of either exported load
helper supply its actual sink call on the instruction matched at the input.
The intermediate sink update and installed load-format provenance are derived. -/
theorem stock_loadSink_call {ctx : Ctx} {st matched next : State}
    {tr tr' tr'' : Array RuleId} {bound : Isle.Interp.Env V} {ii n m : Nat}
    {ty : CTy} {out : V} (atomic : Bool)
    (hm : (matchRule program (Stock.sem ctx) {} (n + 1)
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst ii] else [.ty ty, .inst ii])).run (st, tr) =
        .ok (some bound, matched, tr'))
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 5)
      (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched, tr') =
        .ok (some out, next, tr'')) :
    ∃ sunk info fields,
      Stock.externCtor ctx T.sink_inst [.inst ii] st = .ok (.op .unit, sunk) ∧
      sunk = { st with color := some st.entryColor[ii]!, sunk := st.sunk.set! ii true } ∧
      ctx.insts[ii]? = some info ∧
      (Backend.sem ctx).unData 152 info.data = some (if atomic then 17 else 16, fields) := by
  obtain ⟨info, fields, hi, hf⟩ := stock_loadSink_pattern atomic hm
  obtain ⟨hstate, htrace, hk⟩ := stock_loadSink_binding atomic hm
  subst matched
  subst tr'
  have hcall : ∃ sunk, Stock.externCtor ctx T.sink_inst [.inst ii] st =
      .ok (.op .unit, sunk) := by
    cases atomic with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, rule_inst_4203] at hs
      obtain ⟨unit, sunk, trace, he⟩ := rhs_sink_receipt hs
      exact ⟨sunk, sink_call_receipt hk he⟩
    | true =>
      simp only [↓reduceIte, rule_inst_3905] at hs
      obtain ⟨unit, sunk, trace, he⟩ := rhs_sink_receipt hs
      exact ⟨sunk, sink_call_receipt hk he⟩
  obtain ⟨sunk, hc⟩ := hcall
  exact ⟨sunk, info, fields, hc, (sink_accepted hc).2.2.2.2, hi, hf⟩

private def patternCtx (atomic : Bool) : Ctx := { sinkCtx with insts := #[
  ⟨(instData default (if atomic then .atomicLoad .i8 {} 1
    else .load .load .i8 {} 1 0)).toOption.getD (.op .unit), [0], [.int 8],
    some (if atomic then .atomicLoad .i8 {} 1 else .load .load .i8 {} 1 0)⟩] }

private def patternMatchOk (atomic : Bool) : Bool :=
  match (matchRule program (Stock.sem (patternCtx atomic)) {} 2
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) with
  | .ok (some _, _, _) => true
  | _ => false

private theorem patternMatchOk_true (atomic : Bool) : patternMatchOk atomic = true := by
  cases atomic <;> decide +kernel

/-- Neither actual load-pattern sink helper can match an installed explicit
trap terminator slot. This is a matcher fact, not a whole-evaluator invariant. -/
theorem stock_loadSink_trap_nomatch {ctx : Ctx} {st matched : State}
    {tr tr' : Array RuleId} {bound : Isle.Interp.Env V} {ii n : Nat} {ty : CTy}
    {c : Clif.TrapCode}
    (hi : ctx.insts[ii]? = some
      ⟨.data 152 26 [.data 151 4 [], .op (.trapCode c)], [], [], none⟩)
    (atomic : Bool) :
    (matchRule program (Stock.sem ctx) {} (n + 1)
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst ii] else [.ty ty, .inst ii])).run (st, tr) ≠
        .ok (some bound, matched, tr') := by
  intro hm
  obtain ⟨info, fields, hinfo, hf⟩ := stock_loadSink_pattern atomic hm
  have he := Option.some.inj (hi.symm.trans hinfo)
  subst info
  cases atomic <;> simp [Backend.sem] at hf

/-- Both exported helpers match installed real load data after the raw offset32
extractor fix; the provenance premise is inhabited in both cases. -/
theorem stock_loadSink_pattern_witness (atomic : Bool) :
    ∃ bound matched trace info fields,
      (matchRule program (Stock.sem (patternCtx atomic)) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) =
          .ok (some bound, matched, trace) ∧
      (patternCtx atomic).insts[0]? = some info ∧
      (Backend.sem (patternCtx atomic)).unData 152 info.data =
        some (if atomic then 17 else 16, fields) := by
  have h := patternMatchOk_true atomic
  unfold patternMatchOk at h
  split at h
  · rename_i bound matched trace hm
    obtain ⟨info, fields, hi, hf⟩ := stock_loadSink_pattern (n := 1) atomic hm
    exact ⟨bound, matched, trace, info, fields, hm, hi, hf⟩
  · cases h

/-- Both actual exported helper matches provide their retained instruction
binding and unchanged state/trace, inhabiting the binding-provenance premises. -/
theorem stock_loadSink_binding_witness (atomic : Bool) :
    ∃ bound,
      (matchRule program (Stock.sem (patternCtx atomic)) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) =
          .ok (some bound, sinkState, #[]) ∧
      bound[if atomic then 1 else 3]? = some (some (.inst 0)) := by
  obtain ⟨bound, matched, trace, _, _, hm, _, _⟩ := stock_loadSink_pattern_witness atomic
  obtain ⟨hs, ht, hb⟩ := stock_loadSink_binding (n := 1) atomic hm
  subst matched
  subst trace
  exact ⟨bound, hm, hb⟩

private def patternFullOk (atomic : Bool) : Bool :=
  match (matchRule program (Stock.sem (patternCtx atomic)) {} 2
      (if atomic then rule_inst_3905 else rule_inst_4203)
      (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) with
  | .ok (some bound, matched, trace) =>
    match (evalExpr program (Stock.sem (patternCtx atomic)) {} 2005
        (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched, trace) with
    | .ok (some _, final, _) => final.sunk[0]!
    | _ => false
  | _ => false

private theorem patternFullOk_true (atomic : Bool) : patternFullOk atomic = true := by
  cases atomic <;> decide +kernel

/-- Both real exported helpers match and execute their complete RHSs, marking
an actual load sunk and inhabiting the full sink-call provenance theorem. -/
theorem stock_loadSink_call_witness (atomic : Bool) :
    ∃ bound matched next trace trace' out sunk,
      (matchRule program (Stock.sem (patternCtx atomic)) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) =
          .ok (some bound, matched, trace) ∧
      (evalExpr program (Stock.sem (patternCtx atomic)) {} 2005
        (if atomic then rule_inst_3905 else rule_inst_4203).rhs bound).run (matched, trace) =
          .ok (some out, next, trace') ∧ next.sunk[0]! = true ∧
      Stock.externCtor (patternCtx atomic) T.sink_inst [.inst 0] sinkState =
        .ok (.op .unit, sunk) ∧
      sunk = { (sinkState) with color := some sinkState.entryColor[0]!, sunk := sinkState.sunk.set! 0 true } := by
  have h := patternFullOk_true atomic
  unfold patternFullOk at h
  split at h
  · rename_i bound matched trace hm
    split at h
    · rename_i out next trace' hs
      obtain ⟨sunk, _, _, hc, hn, _, _⟩ := stock_loadSink_call (n := 1) (m := 2000) atomic hm hs
      exact ⟨bound, matched, next, trace, trace', out, sunk, hm, hs, h, hc, hn⟩
    · cases h
  · cases h

/-- An installed positive-code trap slot inhabits both helper-exclusion cases. -/
theorem stock_loadSink_trap_nomatch_witness :
    ∃ ctx : Ctx, ctx.insts[0]? = some
      ⟨.data 152 26 [.data 151 4 [], .op (.trapCode (.user 7))], [], [], none⟩ ∧
      ∀ atomic : Bool,
      (matchRule program (Stock.sem ctx) {} 2
        (if atomic then rule_inst_3905 else rule_inst_4203)
        (if atomic then [.inst 0] else [.ty (.int 8), .inst 0])).run (sinkState, #[]) ≠
          .ok (some #[], sinkState, #[]) := by
  let ctx : Ctx := { sinkCtx with insts := #[
    ⟨.data 152 26 [.data 151 4 [], .op (.trapCode (.user 7))], [], [], none⟩] }
  have hi : ctx.insts[0]? = some
      ⟨.data 152 26 [.data 151 4 [], .op (.trapCode (.user 7))], [], [], none⟩ := rfl
  exact ⟨ctx, hi, fun atomic => stock_loadSink_trap_nomatch hi atomic⟩

end Backend.Stock.Proof

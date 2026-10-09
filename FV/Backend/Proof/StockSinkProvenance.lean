import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.IselGeneric

/-! Successful eligible-source extraction followed by effect sinking identifies
an actual single-result producer. This is an internal helper invariant for
classifying terminator scans, not an additional source/checker condition. -/
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
attribute [local irreducible] Isle.Aarch64.program

/-- Actual extraction and sink success jointly discharge the positive-color
premise of source eligibility. Result-less terminator slots cannot inhabit this
successful helper sequence. Rule evaluation must still supply the connection
between these two calls for each selected sinking rule. -/
theorem stock_sink_resultful {ctx : Ctx} {v i : Nat} {input matched next : State}
    (he : Stock.externCtor ctx T.is_sinkable_inst [.value v] input = .ok (.inst i, matched))
    (hs : Stock.externCtor ctx T.sink_inst [.inst i] matched = .ok (.op .unit, next)) :
    matched = input ∧ ctx.defInst? v = some i ∧ input.uses[v]! = .once ∧
      ctx.insts[i]!.results.length = 1 ∧
      next = { input with color := some input.entryColor[i]!, sunk := input.sunk.set! i true } := by
  have hsource : source ctx input v = some (i, true) ∧ matched = input := by
    change (match source ctx input v with
      | some (j, true) => ExtResult.ok (V.inst j, input)
      | _ => ExtResult.fail) = ExtResult.ok (V.inst i, matched) at he
    cases hv : source ctx input v with
    | none => rw [hv] at he; cases he
    | some pair =>
      obtain ⟨j, eligible⟩ := pair
      cases eligible with
      | false => rw [hv] at he; cases he
      | true =>
        rw [hv] at he
        cases he
        exact ⟨rfl, rfl⟩
  obtain ⟨hsource, rfl⟩ := hsource
  have haccepted := sink_accepted hs
  have heligible := source_effect_eligible hsource haccepted.1
  exact ⟨rfl, heligible.1, heligible.2.1, heligible.2.2.1, haccepted.2.2.2.2⟩

/-- The actual eligibility if-let used by extension-load rules binds precisely
its returned instruction, retains state/trace, and supplies the extraction
receipt required by the sinking invariant. -/
theorem stock_sink_iflet {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env bound : Isle.Interp.Env V} {x k v n : Nat}
    (hv : env[x]? = some (some (.value v)))
    (h : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, next, tr')) :
    ∃ i, Stock.externCtor ctx T.is_sinkable_inst [.value v] st = .ok (.inst i, st) ∧
      next = st ∧ tr' = tr ∧ bound[k]? = some (some (.inst i)) := by
  simp only [matchIfLets.eq_3, evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2,
    evalArgs.eq_2, hv, isel_monad] at h
  simp only [applyTerm.eq_2, data_program.t221, T.is_sinkable_inst,
    Stock.sem, Stock.externCtor, isel_monad] at h
  cases he : source ctx st v with
  | none => simp only [he, isel_monad] at h; cases h
  | some pair =>
    obtain ⟨i, eligible⟩ := pair
    cases eligible with
    | false => simp only [he, isel_monad] at h; cases h
    | true =>
      simp only [he, isel_monad, matchPat] at h
      split at h
      · rename_i hk
        simp only [isel_monad, matchIfLets.eq_2,
          Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨i, ?_, rfl, rfl, ?_⟩
        · change (match source ctx st v with
            | some (j, true) => ExtResult.ok (V.inst j, st)
            | _ => ExtResult.fail) = ExtResult.ok (V.inst i, st)
          rw [he]
        · simp [hk]
      · cases h

/-- Actual if-let evaluation and evaluation of the later sink expression tie
its target to the extracted producer, rather than assuming paired helper calls. -/
theorem stock_iflet_sink_resultful {ctx : Ctx} {st matched next : State}
    {tr tr' tr'' : Array RuleId} {env bound : Isle.Interp.Env V} {x k v n m : Nat} {out : V}
    (hv : env[x]? = some (some (.value v)))
    (hi : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, matched, tr'))
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 3)
      (.term 13 236 [.var 18 k]) bound).run (matched, tr') =
        .ok (some out, next, tr'')) :
    ∃ i, ctx.defInst? v = some i ∧ st.uses[v]! = .once ∧
      ctx.insts[i]!.results.length = 1 ∧ out = .op .unit ∧ tr'' = tr ∧
      next = { st with color := some st.entryColor[i]!, sunk := st.sunk.set! i true } := by
  obtain ⟨i, he, hm, ht, hk⟩ := stock_sink_iflet hv hi
  subst matched
  subst tr'
  simp only [evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2, evalArgs.eq_2,
    hk, isel_monad, applyTerm.eq_2, data_program.t236, T.sink_inst, Stock.sem] at hs
  cases hc : Stock.externCtor ctx T.sink_inst [.inst i] st with
  | fail => simp only [T.sink_inst] at hc; rw [hc] at hs; simp only [isel_monad] at hs; cases hs
  | unmodeled e => simp only [T.sink_inst] at hc; rw [hc] at hs; simp only [isel_monad] at hs; cases hs
  | ok pair =>
    obtain ⟨value, final⟩ := pair
    have haccepted := sink_accepted hc
    obtain ⟨_, _, _, rfl, rfl⟩ := haccepted
    have hc' := hc
    simp only [T.sink_inst] at hc'
    rw [hc'] at hs
    simp only [isel_monad, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    have h := stock_sink_resultful he hc
    exact ⟨i, h.2.1, h.2.2.1, h.2.2.2.1, rfl, rfl, h.2.2.2.2⟩

private theorem eligibility_ctor (ctx : Ctx) (st : State) (a : V) :
    Stock.externCtor ctx T.is_sinkable_inst [a] st =
      match a with
      | .value v => match source ctx st v with
        | some (i, true) => ExtResult.ok (V.inst i, st)
        | _ => ExtResult.fail
      | _ => ExtResult.fail := by
  cases a <;> rfl

private theorem iflet_value {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env bound : Isle.Interp.Env V} {x k n : Nat}
    (h : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, next, tr')) :
    ∃ v, env[x]? = some (some (.value v)) := by
  simp only [matchIfLets.eq_3, evalExpr.eq_7, evalArgs.eq_3, evalExpr.eq_2,
    evalArgs.eq_2, isel_monad] at h
  cases hv : env[x]? with
  | none => rw [hv] at h; simp only [isel_monad] at h; cases h
  | some value =>
    cases value with
    | none => rw [hv] at h; simp only [isel_monad] at h; cases h
    | some value =>
      cases hvv : value with
      | value v => exact ⟨v, rfl⟩
      | _ =>
        rw [hv] at h
        simp only [isel_monad, applyTerm.eq_2, data_program.t221,
          Stock.sem, isel_data, isel_monad] at h
        have hf : Stock.externCtor ctx T.is_sinkable_inst [value] st = .fail := by
          rw [eligibility_ctor, hvv]
        rw [hf] at h
        simp only [isel_monad] at h
        cases h

private theorem sink_rhs_receipt {ctx : Ctx} {st next : State} {tr tr' : Array RuleId}
    {env : Isle.Interp.Env V} {m j k ty : Nat} {body : Expr} {out : V}
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 5)
      (.let ty [(j, 13, .term 13 236 [.var 18 k])] body) env).run (st, tr) =
        .ok (some out, next, tr')) :
    ∃ unit sunk trace,
      (evalExpr program (Stock.sem ctx) {} (m + 3)
        (.term 13 236 [.var 18 k]) env).run (st, tr) =
          .ok (some unit, sunk, trace) := by
  rw [evalExpr.eq_6] at hs
  rw [evalBinds.eq_3] at hs
  simp only [isel_monad] at hs
  cases he : (evalExpr program (Stock.sem ctx) {} (m + 3)
      (.term 13 236 [.var 18 k]) env).run (st, tr) with
  | error e => rw [he] at hs; cases hs
  | ok pair =>
    obtain ⟨value, state⟩ := pair
    cases value with
    | none => rw [he] at hs; simp only [isel_monad] at hs; cases hs
    | some unit => exact ⟨unit, state.1, state.2, rfl⟩

/-- A successful complete RHS with the extension rules' leading sink binding
supplies the sink-expression subexecution automatically. -/
theorem stock_iflet_rhs_sink_resultful {ctx : Ctx} {st matched next : State}
    {tr tr' tr'' : Array RuleId} {env bound : Isle.Interp.Env V}
    {x k j ty v n m : Nat} {body : Expr} {out : V}
    (hv : env[x]? = some (some (.value v)))
    (hi : (matchIfLets program (Stock.sem ctx) {} (n + 4)
      [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩] env).run (st, tr) =
        .ok (some bound, matched, tr'))
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 5)
      (.let ty [(j, 13, .term 13 236 [.var 18 k])] body) bound).run (matched, tr') =
        .ok (some out, next, tr'')) :
    ∃ i sunk, ctx.defInst? v = some i ∧ st.uses[v]! = .once ∧
      ctx.insts[i]!.results.length = 1 ∧
      sunk = { st with color := some st.entryColor[i]!, sunk := st.sunk.set! i true } := by
  obtain ⟨unit, sunk, trace, hcall⟩ := sink_rhs_receipt hs
  obtain ⟨i, hd, hu, hl, _, _, hn⟩ := stock_iflet_sink_resultful hv hi hcall
  exact ⟨i, sunk, hd, hu, hl, hn⟩

/-- Complete successful matching and RHS evaluation of a rule with the actual
extension-load eligibility/sink shape identify the resultful sink target. Neither
eligibility bindings nor sink subexecutions are supplied by the caller. -/
theorem stock_matched_rule_sink_resultful {ctx : Ctx} {st matched next : State}
    {tr tr' tr'' : Array RuleId} {bound : Isle.Interp.Env V}
    {x k j ty n m : Nat} {body : Expr} {out : V} {r : Rule} {vs : List V}
    (hil : r.iflets = [⟨.bind 18 k (.wildcard 18), .term 18 221 [.var 15 x]⟩])
    (hrhs : r.rhs = .let ty [(j, 13, .term 13 236 [.var 18 k])] body)
    (hm : (matchRule program (Stock.sem ctx) {} (n + 5) r vs).run (st, tr) =
      .ok (some bound, matched, tr'))
    (hs : (evalExpr program (Stock.sem ctx) {} (m + 5) r.rhs bound).run (matched, tr') =
      .ok (some out, next, tr'')) :
    ∃ v i sunk, ctx.defInst? v = some i ∧ st.uses[v]! = .once ∧
      ctx.insts[i]!.results.length = 1 ∧
      sunk = { st with color := some st.entryColor[i]!, sunk := st.sunk.set! i true } := by
  obtain ⟨env, _, hi⟩ := matchRule_some_inv hm
  rw [hil] at hi
  obtain ⟨v, hv⟩ := iflet_value hi
  rw [hrhs] at hs
  obtain ⟨i, sunk, hd, hu, hl, hn⟩ := stock_iflet_rhs_sink_resultful hv hi hs
  exact ⟨v, i, sunk, hd, hu, hl, hn⟩

/-- The real extension-load eligibility if-let and its later sink expression
both execute on the load fixture; state and target provenance are inhabited. -/
theorem stock_sink_iflet_witness :
    ∃ bound next,
      (matchIfLets program (Stock.sem sinkCtx) {} 4
        [⟨.bind 18 5 (.wildcard 18), .term 18 221 [.var 15 4]⟩]
        #[none, none, none, none, some (.value 0), none, none]).run (sinkState, #[]) =
          .ok (some bound, sinkState, #[]) ∧
      bound[5]? = some (some (.inst 0)) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 3
        (.term 13 236 [.var 18 5]) bound).run (sinkState, #[]) =
          .ok (some (.op .unit), next, #[]) ∧ next = sinkNext := by
  refine ⟨#[none, none, none, none, some (.value 0), some (.inst 0), none], sinkNext,
    ?_, rfl, ?_, rfl⟩
  all_goals
    simp only [matchIfLets, evalExpr, evalArgs, applyTerm, matchPat,
      data_program.t221, data_program.t236, Stock.sem, isel_data, isel_monad]
    rfl

private def extensionInput : Isle.Interp.Env V :=
  #[some (.ty (.int 8)), some (.value 1), some (.op (.memFlags {})),
    some (.int 0), some (.value 0), none, none]

private def extensionRhsOk : Bool :=
  match (matchIfLets program (Stock.sem sinkCtx) {} 4
      rule_lower_1300.iflets extensionInput).run (sinkState, #[]) with
  | .ok (some bound, matched, tr) =>
    match (evalExpr program (Stock.sem sinkCtx) {} 1005
        rule_lower_1300.rhs bound).run (matched, tr) with
    | .ok (some _, _, _) => true
    | _ => false
  | _ => false

private theorem extensionRhsOk_true : extensionRhsOk = true := by
  decide +kernel

/-- The actual exported uextend-load RHS succeeds after its actual eligibility
if-let; the complete-RHS provenance theorem identifies the sunk producer. -/
theorem stock_iflet_rhs_sink_resultful_witness :
    ∃ bound matched next tr tr' out i sunk,
      (matchIfLets program (Stock.sem sinkCtx) {} 4
        rule_lower_1300.iflets extensionInput).run (sinkState, #[]) =
          .ok (some bound, matched, tr) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 1005
        rule_lower_1300.rhs bound).run (matched, tr) = .ok (some out, next, tr') ∧
      sinkCtx.defInst? 0 = some i ∧ sinkState.uses[0]! = .once ∧
      sinkCtx.insts[i]!.results.length = 1 ∧
      sunk = { (sinkState) with color := some sinkState.entryColor[i]!, sunk := sinkState.sunk.set! i true } := by
  have h := extensionRhsOk_true
  unfold extensionRhsOk at h
  split at h
  · rename_i bound matched tr hi
    split at h
    · rename_i out next tr' hs
      have hv : extensionInput[4]? = some (some (.value 0)) := rfl
      obtain ⟨i, sunk, hd, hu, hl, hn⟩ := stock_iflet_rhs_sink_resultful
        (n := 0) (m := 1000) hv hi hs
      exact ⟨bound, matched, next, tr, tr', out, i, sunk, hi, hs, hd, hu, hl, hn⟩
    · cases h
  · cases h

private def matchedExtensionCtx : Ctx := { sinkCtx with
  insts := #[
    ⟨(instData default (.load .load .i8 {} 1 0)).toOption.getD (.op .unit), [0], [.int 8],
      some (.load .load .i8 {} 1 0)⟩,
    ⟨(instData default (.extend .uextend .i64 0)).toOption.getD (.op .unit), [2], [.int 64],
      some (.extend .uextend .i64 0)⟩] }

private def matchedExtensionOk : Bool :=
  match (matchRule program (Stock.sem matchedExtensionCtx) {} 5
      rule_lower_1300 [.inst 1]).run (sinkState, #[]) with
  | .ok (some bound, matched, tr) =>
    match (evalExpr program (Stock.sem matchedExtensionCtx) {} 1005
        rule_lower_1300.rhs bound).run (matched, tr) with
    | .ok (some _, _, _) => true
    | _ => false
  | _ => false

private theorem matchedExtensionOk_true : matchedExtensionOk = true := by
  decide +kernel

/-- The actual exported uextend-load rule successfully matches real installed
load/extension data and evaluates its full RHS, inhabiting the full-rule theorem. -/
theorem stock_matched_rule_sink_resultful_witness :
    ∃ bound matched next tr tr' out v i sunk,
      (matchRule program (Stock.sem matchedExtensionCtx) {} 5
        rule_lower_1300 [.inst 1]).run (sinkState, #[]) = .ok (some bound, matched, tr) ∧
      (evalExpr program (Stock.sem matchedExtensionCtx) {} 1005
        rule_lower_1300.rhs bound).run (matched, tr) = .ok (some out, next, tr') ∧
      matchedExtensionCtx.defInst? v = some i ∧ sinkState.uses[v]! = .once ∧
      matchedExtensionCtx.insts[i]!.results.length = 1 ∧
      sunk = { (sinkState) with color := some sinkState.entryColor[i]!, sunk := sinkState.sunk.set! i true } := by
  have h := matchedExtensionOk_true
  unfold matchedExtensionOk at h
  split at h
  · rename_i bound matched tr hm
    split at h
    · rename_i out next tr' hs
      obtain ⟨v, i, sunk, hd, hu, hl, hn⟩ := stock_matched_rule_sink_resultful
        (n := 0) (m := 1000) rfl rfl hm hs
      exact ⟨bound, matched, next, tr, tr', out, v, i, sunk, hm, hs, hd, hu, hl, hn⟩
    · cases h
  · cases h

/-- The interpreter-level provenance theorem's actual successful premises
produce the single-result producer on the same fixture. -/
theorem stock_iflet_sink_resultful_witness :
    ∃ env bound next, env[4]? = some (some (V.value 0)) ∧
      (matchIfLets program (Stock.sem sinkCtx) {} 4
        [⟨.bind 18 5 (.wildcard 18), .term 18 221 [.var 15 4]⟩] env).run (sinkState, #[]) =
          .ok (some bound, sinkState, #[]) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 3
        (.term 13 236 [.var 18 5]) bound).run (sinkState, #[]) =
          .ok (some (.op .unit), next, #[]) ∧
      ∃ i, sinkCtx.defInst? 0 = some i ∧ sinkState.uses[0]! = .once ∧
        sinkCtx.insts[i]!.results.length = 1 ∧
        next = { (sinkState) with color := some sinkState.entryColor[i]!, sunk := sinkState.sunk.set! i true } := by
  obtain ⟨bound, next, hi, _, hs, _⟩ := stock_sink_iflet_witness
  have hv : (#[none, none, none, none, some (V.value 0), none, none] : Isle.Interp.Env V)[4]? =
      some (some (.value 0)) := rfl
  obtain ⟨i, hd, hu, hl, _, _, hn⟩ := stock_iflet_sink_resultful hv hi hs
  exact ⟨_, bound, next, hv, hi, hs, i, hd, hu, hl, hn⟩

/-- A real eligible load executes both actual helper calls and is marked sunk;
the successful extraction/sinking premises are jointly inhabited. -/
theorem stock_sink_resultful_witness :
    Stock.externCtor sinkCtx T.is_sinkable_inst [.value 0] sinkState = .ok (.inst 0, sinkState) ∧
      Stock.externCtor sinkCtx T.sink_inst [.inst 0] sinkState = .ok (.op .unit, sinkNext) ∧
      sinkCtx.defInst? 0 = some 0 ∧ sinkState.uses[0]! = .once ∧
      sinkCtx.insts[0]!.results.length = 1 ∧ sinkNext.sunk[0]! = true := by
  have he : Stock.externCtor sinkCtx T.is_sinkable_inst [.value 0] sinkState =
      .ok (.inst 0, sinkState) := rfl
  have h := stock_sink_resultful he sink_ctor_eq_witness
  exact ⟨he, sink_ctor_eq_witness, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

end Backend.Stock.Proof

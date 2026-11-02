import FV.Backend.Proof.StockDemand
import FV.Backend.Proof.IselCtlBase
import FV.Backend.Proof.StockReturnABI

/-! The real lower_return helper uses mapped vector requests and the revised
Stock ABI constructor. Full scheduling state and ordered requests are retained. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem output_none (ctx : Ctx) (st : State) (value : V) (next : State) :
    Stock.externCtor ctx T.output_none [] st = .ok (value,next) ↔ value = .regsVec [] ∧ next = st := by
  have unchanged : Stock.externCtor ctx T.output_none [] st = .ok (.regsVec [],st) := rfl
  rw [unchanged]
  simp [eq_comm]

private theorem return_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl

/-- The actual internal helper294 derives its source requests, mapped registers,
pins, exact return code and complete demand-marked Stock state. -/
theorem stock_lower_return_observed {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel : Nat} (enough : 60 ≤ fuel) {xs : List Nat}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 25 294 [.values xs] (st,tr) out (next,trace)) :
    ∃ rs ps,(∀ x ∈ xs,DemandAllowed ctx st x) ∧ xs.mapM ctx.valueReg? = some rs ∧
      returnPins ctx.func rs.length = some ps ∧
      next = {xs.foldl State.mark st with base := (xs.foldl State.mark st).base.emit (.rets (rs.zip ps))} ∧
      out = .regsVec [] := by
  obtain ⟨_,_,_,hL,hpre,_,_,_,_,_,_,hm,he,stateEq,fuelEq⟩ :=
    return_internal_split_first hc hp.t294 term_294_kind rfl (by rw [hp.r294]; simp; omega) run
  rcases Prod.mk.inj stateEq with ⟨rfl,rfl⟩
  cases fuelEq
  rw [hp.r294] at hL
  isel_rule_cases hL
  cases hp
  isel_inv [*,rule_prelude_lower_1493,sem_ctor,sem_extract,ext_value_list_slice_iff,output_none] at hm he
  isel_destruct
  subst_vars
  isel_inv_simp [stock_put_in_regs_vec_iff,output_none] at *
  isel_destruct
  subst_vars
  rename_i genCall
  obtain ⟨unpacked,ps,pins,unpack,state,unitEq⟩ := stock_gen_return_shape genCall
  change List.mapM single? (List.map (fun r => [r]) _) = some unpacked at unpack
  rw [mapM_single_map] at unpack
  cases unpack
  exact ⟨by assumption,_,by assumption,ps,by simpa only [List.length_map] using pins,state,rfl⟩

/-- Construct the actual ABI return from a derived pin selection. -/
theorem stock_gen_return_call (ctx : Ctx) (st : State) (rs ps : List Reg)
    (pins : returnPins ctx.func rs.length = some ps) :
    Stock.externCtor ctx T.gen_return [.regsVec (rs.map (fun r => [r]))] st =
      .ok (.op .unit,{st with base := st.base.emit (.rets (rs.zip ps))}) := by
  change (match returnPins ctx.func (rs.map (fun r => [r])).length,unpackReturnRegs (rs.map (fun r => [r])) with
    | some ps,some rs => (ExtResult.ok (.op .unit,{st with base := st.base.emit (.rets (rs.zip ps))}) : ExtResult (V × State))
    | _,_ => ExtResult.unmodeled "gen_return register count") = _
  have unpack : unpackReturnRegs (rs.map (fun r => [r])) = some rs := by
    change List.mapM single? (rs.map (fun r => [r])) = some rs
    exact mapM_single_map rs
  rw [List.length_map,pins,unpack]

/-- The real return helper also succeeds constructively for safe original
requests, with exact complete state and fired rule. This supports completeness;
its source/ABI caller derives safety, mapping and pins internally. -/
theorem stock_lower_return_call {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (xs : List Nat) (rs ps : List Reg)
    (st : State) (tr : Array RuleId) (n : Nat)
    (safe : ∀ x ∈ xs,DemandAllowed ctx st x) (mapped : xs.mapM ctx.valueReg? = some rs)
    (pins : returnPins ctx.func rs.length = some ps) :
    (applyTerm p (Stock.sem ctx) cfg (n+60) 25 294 [.values xs]).run (st,tr) =
      .ok (some (.regsVec []),{xs.foldl State.mark st with
        base := (xs.foldl State.mark st).base.emit (.rets (rs.zip ps))},tr.push rule_prelude_lower_1493.id) := by
  have requested := stock_put_in_regs_vec ctx st xs rs safe mapped
  have returned := stock_gen_return_call ctx (xs.foldl State.mark st) rs ps pins
  have outputCall (before : State) : Stock.externCtor ctx T.output_none [] before = .ok (.regsVec [],before) := rfl
  cases hp
  isel_eval [*,rule_prelude_lower_1493,sem_ctor,sem_extract]
end Backend.Stock.Proof

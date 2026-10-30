import FV.Backend.Proof.StockSelectObserved
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty k j : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data k j vs) = if k = ty then some (j,vs) else none :=
  Backend.Proof.sem_unData ctx ty k j vs
private theorem zero (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]
  rfl
private theorem select_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
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

private def zeroEnv (w x y key : Nat) (size : OperandSize) : Isle.Interp.Env V :=
  #[some (.ty (.int w)),some (.reg (.vreg key .int)),
    some (.data 93 (if size = .size32 then 0 else 1) []),some (.value x),some (.value y)]
private theorem zero_match {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (w x y key : Nat) (size : OperandSize) (nonzero : Bool) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) (if nonzero then rule_inst_5322 else rule_inst_5320)
      [.ty (.int w),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg key .int),.data 93 (if size = .size32 then 0 else 1) []],.value x,.value y]).run (st,tr) =
      .ok (some (zeroEnv w x y key size),st,tr) := by
  cases nonzero <;> cases hp
  all_goals isel_eval [*,rule_inst_5320,rule_inst_5322,zeroEnv,sem_unData,stock_matchArgs]
  all_goals rfl
private theorem wrong_match {p : Program} (hp : Data p) (ctx : Ctx) (cfg : Config)
    (w x y key : Nat) (size : OperandSize) (nonzero : Bool) {r : Rule}
    (member : r ∈ [if nonzero then rule_inst_5320 else rule_inst_5322,rule_inst_5324])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) r
      [.ty (.int w),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg key .int),.data 93 (if size = .size32 then 0 else 1) []],.value x,.value y]).run (st,tr) =
      .ok (none,st,tr) := by
  cases nonzero <;> simp only [Bool.false_eq_true,ite_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  all_goals rcases member with rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_5320,rule_inst_5322,rule_inst_5324,sem_unData,stock_matchArgs]
/-- Successful actual Zero/NotZero select derives its guarded operand requests,
register-zero comparison, output and complete scheduling state. -/
theorem stock_select_zero_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel w x y : Nat} (enough : 319 ≤ fuel)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (nonzero : Bool) (size : OperandSize) (key : Nat)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 659
      [.ty (.int w),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg key .int),.data 93 (if size = .size32 then 0 else 1) []],.value x,.value y]
      (st,tr) out (next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regs [(st.base.fresh .int).1] ∧
        next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit (cmpXzr size key)).emit
          (.csel (st.base.fresh .int).1 rx ry (if nonzero then .ne else .eq)))} := by
  obtain ⟨pre,r,post,order,prior,k,n,env,s1,after,trace',matched,rhs,final,fuelEq⟩ :=
    select_internal_split_first hc hp.t659 term_659_kind rfl (by rw [hp.r659]; simp; omega) run
  rw [hp.r659] at order
  have selected : r = if nonzero then rule_inst_5322 else rule_inst_5320 := by
    clear width
    cases nonzero
    case false =>
      simp only [Bool.false_eq_true,ite_true,ite_false] at *
      isel_rule_cases order
      all_goals first
        | rfl
        | (have replay := wrong_match hp ctx cfg w x y key size false (r := rule_inst_5322) (by decide +kernel) st tr k
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at matched
           cases matched)
        | (have replay := wrong_match hp ctx cfg w x y key size false (r := rule_inst_5324) (by decide +kernel) st tr k
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at matched
           cases matched)
        | (obtain ⟨q,s2,failed⟩ := prior rule_inst_5320 (by decide +kernel)
           have replay := zero_match hp ctx cfg w x y key size false st tr q
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at failed
           cases failed)
    case true =>
      simp only [Bool.false_eq_true,ite_true,ite_false] at *
      isel_rule_cases order
      all_goals first
        | rfl
        | (have replay := wrong_match hp ctx cfg w x y key size true (r := rule_inst_5320) (by decide +kernel) st tr k
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at matched
           cases matched)
        | (have replay := wrong_match hp ctx cfg w x y key size true (r := rule_inst_5324) (by decide +kernel) st tr k
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at matched
           cases matched)
        | (obtain ⟨q,s2,failed⟩ := prior rule_inst_5322 (by decide +kernel)
           have replay := zero_match hp ctx cfg w x y key size true st tr q
           simp only [Bool.false_eq_true,ite_true,ite_false] at replay
           rw [replay] at failed
           cases failed)
  rw [selected,zero_match hp ctx cfg w x y key size nonzero st tr k] at matched
  cases matched
  have get0 : (zeroEnv w x y key size)[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (zeroEnv w x y key size)[1]? = some (some (.reg (.vreg key .int))) := rfl
  have get2 : (zeroEnv w x y key size)[2]? = some (some (.data 93 (if size = .size32 then 0 else 1) [])) := rfl
  have get3 : (zeroEnv w x y key size)[3]? = some (some (.value x)) := rfl
  have get4 : (zeroEnv w x y key size)[4]? = some (some (.value y)) := rfl
  have decoded : MInst.ofV (.data 58 2 [.data 59 10 [],.data 93 (if size = .size32 then 0 else 1) [],
      .reg .xzr,.reg (.vreg key .int),.reg .xzr]) = some (cmpXzr size key) := by cases size <;> rfl
  cases final
  rw [selected] at rhs
  have saved := hp
  cases nonzero <;> cases hp
  all_goals isel_inv_simp [*,rule_inst_5320,rule_inst_5322,sem_ctor,sem_mkData,zero] at rhs
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [zero,ExtResult.ok.injEq,Prod.mk.injEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals
    rename_i producer builderState st consumerCall buildCall
    have replay := ScalarCmp.stock_cmp_rr_builder saved ctx hc st tr (n-24)
      (.data 93 (if size = .size32 then 0 else 1) []) (.reg (.vreg key .int)) (.reg .xzr)
    have gas : n-24+40 = n+16 := by omega
    unfold ApplyInternal at buildCall
    rw [gas,buildCall] at replay
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
    obtain ⟨rfl,rfl⟩ := replay
    exact stock_select_cond_observed saved ctx hc (by omega) width _ decoded consumerCall
end Backend.Stock.Proof.ScalarSelect

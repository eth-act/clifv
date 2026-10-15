import FV.Backend.Proof.StockSelectRequests
import FV.Backend.Proof.StockSelectConditions
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem int_scalar (ctx : Ctx) {w : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (st : State) :
    Stock.externCtor ctx T.ty_int_ref_scalar_64 [.ty (.int w)] st = .ok (.ty (.int w),st) := by
  rw [stock_ctor_baseOnly ctx T.ty_int_ref_scalar_64 _ st (by decide)]
  rcases width with rfl | rfl | rfl | rfl <;> rfl
private theorem not_float (ctx : Ctx) (w : Nat) (st : LState) :
    Backend.externExtract ctx T.ty_scalar_float (.ty (.int w)) st = .fail := rfl
private theorem not_vector (ctx : Ctx) (w : Nat) (st : LState) :
    Backend.externExtract ctx T.ty_vec128 (.ty (.int w)) st = .fail := rfl
private theorem not_vec64 (ctx : Ctx) (w : Nat) (st : State) :
    Stock.externCtor ctx T.ty_vec64 [.ty (.int w)] st = .fail := by
  rw [stock_ctor_baseOnly ctx T.ty_vec64 _ st (by decide)]
  rfl
private theorem scalar_other_failure {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {w x y : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (mi condition : V)
    {r : Rule} (member : r ∈ [rule_inst_5343,rule_inst_5350,rule_inst_5345,rule_inst_5341,rule_inst_5347])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) r
      [.ty (.int w),.data 47 1 [mi],condition,.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have noFloat : (V.ty (.int w) == V.ty (.float 128)) = false := by
    rcases width with rfl | rfl | rfl | rfl <;> decide
  have no128 : (V.ty (.int w) == V.ty (.int 128)) = false := by
    rcases width with rfl | rfl | rfl | rfl <;> decide
  have noVec := fun q => not_vec64 ctx w q
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_5343,rule_inst_5350,rule_inst_5345,rule_inst_5341,rule_inst_5347,
    sem_ctor,sem_eq,sem_prim,sem_extract,base_eq,base_prim,stock_matchArgs,not_float,not_vector,CTy.ofName?]
private theorem scalar_match {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {w x y : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (mi condition : V)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_inst_5364
      [.ty (.int w),.data 47 1 [mi],condition,.value x,.value y]).run (st,tr) =
      .ok (some (selectEnv w x y mi condition),st,tr) := by
  have scalar := fun q => int_scalar ctx width q
  cases hp
  isel_eval [*,rule_inst_5364,selectEnv,sem_ctor,stock_matchArgs]
  rfl
/-- Actual successful scalar660 derives its unique selected RHS, guarded
requests, result and complete scheduling state internally. -/
theorem stock_select_cond_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel w x y : Nat} (enough : 219 ≤ fuel)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {mi : V} {m : MInst}
    (condition : Cond) (decoded : MInst.ofV mi = some m)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 660
      [.ty (.int w),.data 47 1 [mi],.data 96 condition.idx [],.value x,.value y] (st,tr) out (next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regs [(st.base.fresh .int).1] ∧
        next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))} := by
  obtain ⟨r,member,k,env,s1,after,trace',bound,matched,rhs,final⟩ :=
    applyTerm_internal_some hc hp.t660 term_660_kind rfl run
  rw [hp.r660] at member bound
  obtain ⟨k',rfl⟩ : ∃ k',k = k'+20 := ⟨k-20,by simp only [List.length_cons,List.length_nil] at bound; omega⟩
  have selected : r = rule_inst_5364 := by
    by_cases other : r = rule_inst_5364
    · exact other
    have wrong : r ∈ [rule_inst_5343,rule_inst_5350,rule_inst_5345,rule_inst_5341,rule_inst_5347] := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,other,false_or] using member
    rw [scalar_other_failure hp ctx width mi (.data 96 condition.idx []) wrong st tr k'] at matched
    cases matched
  subst r
  rw [scalar_match hp ctx width mi (.data 96 condition.idx []) st tr k'] at matched
  cases matched
  obtain ⟨n,equal⟩ : ∃ n,fuel = n+120 := ⟨fuel-120,by omega⟩
  rw [equal] at rhs
  have observed := stock_select_rhs_observed hp ctx hc condition decoded rhs
  cases final
  exact observed
private theorem sem_unData (ctx : Ctx) (ty k j : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data k j vs) = if k = ty then some (j,vs) else none :=
  Backend.Proof.sem_unData ctx ty k j vs
private theorem flags_other_failure {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (w x y : Nat) (mi condition : V) {r : Rule} (member : r ∈ [rule_inst_5320,rule_inst_5322])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) r
      [.ty (.int w),.data 123 2 [.data 47 1 [mi],condition],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals cases hp
  all_goals isel_eval [*,rule_inst_5320,rule_inst_5322,sem_unData,stock_matchArgs]
private theorem flags_match {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (w x y : Nat) (mi condition : V) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n+20) rule_inst_5324
      [.ty (.int w),.data 123 2 [.data 47 1 [mi],condition],.value x,.value y]).run (st,tr) =
      .ok (some (selectEnv w x y mi condition),st,tr) := by
  cases hp
  isel_eval [*,rule_inst_5324,sem_unData,stock_matchArgs,selectEnv]
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

/-- First-match selection of actual659 explicit flags reaches scalar660;
the request guards, mapped operands, result and all state fields follow from
the successful original call rather than caller request certificates. -/
theorem stock_select_flags_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel w x y : Nat} (enough : 279 ≤ fuel)
    (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {mi : V} {m : MInst}
    (condition : Cond) (decoded : MInst.ofV mi = some m)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) cfg fuel 22 659
      [.ty (.int w),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value x,.value y] (st,tr) out (next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regs [(st.base.fresh .int).1] ∧
        next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))} := by
  obtain ⟨pre,r,post,order,prior,k,n,env,s1,after,trace',matched,rhs,final,fuelEq⟩ :=
    select_internal_split_first hc hp.t659 term_659_kind rfl (by rw [hp.r659]; simp; omega) run
  rw [hp.r659] at order
  have selected : r = rule_inst_5324 := by
    isel_rule_cases order
    all_goals first
      | rfl
      | (rw [flags_other_failure hp ctx _ x y mi (.data 96 condition.idx []) (by decide +kernel) st tr k] at matched; cases matched)
      | (obtain ⟨q,s2,failed⟩ := prior rule_inst_5324 (by simp)
         rw [flags_match hp ctx _ x y mi (.data 96 condition.idx []) st tr q] at failed
         cases failed)
  subst r
  rw [flags_match hp ctx w x y mi (.data 96 condition.idx []) st tr k] at matched
  cases matched
  have get0 : (selectEnv w x y mi (.data 96 condition.idx []))[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (selectEnv w x y mi (.data 96 condition.idx []))[1]? = some (some (.data 47 1 [mi])) := rfl
  have get2 : (selectEnv w x y mi (.data 96 condition.idx []))[2]? = some (some (.data 96 condition.idx [])) := rfl
  have get3 : (selectEnv w x y mi (.data 96 condition.idx []))[3]? = some (some (.value x)) := rfl
  have get4 : (selectEnv w x y mi (.data 96 condition.idx []))[4]? = some (some (.value y)) := rfl
  have call : ApplyInternal p (Stock.sem ctx) cfg (n+18) 22 660
      [.ty (.int w),.data 47 1 [mi],.data 96 condition.idx [],.value x,.value y] (st,tr) out (after,trace') := by
    exact rhs
  have observed := stock_select_cond_observed hp ctx hc (by omega) width condition decoded call
  cases final
  exact observed
end Backend.Stock.Proof.ScalarSelect

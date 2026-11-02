import FV.Backend.Proof.StockCmpMatchedZero
import FV.Backend.Proof.StockCmpMatchedRegister
import FV.Backend.Proof.StockCmpMatchedImmediate
import FV.Backend.Proof.StockCmpNarrowImmediateObserved
import FV.Backend.Proof.StockCmpNarrowRhsObserved
import FV.Backend.Proof.StockMinMaxRegisterRuns
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem base_eq (ctx : Ctx) (a b : V) : (Backend.sem ctx).eq a b = (a == b) := rfl
private theorem base_prim (ctx : Ctx) (name : String) :
    (Backend.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem narrow128_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5142
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have not128 : (V.ty (.int (if half then 16 else 8)) == V.ty (.int 128)) = false := by cases half <;> decide
  cases hp
  cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5142,sem_extract,sem_unData,sem_eq,sem_prim,
    stock_matchArgs,base_eq,base_prim,CTy.ofName?]
private theorem narrow_scalar_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8))) {r : Rule}
    (member : r ∈ [rule_inst_5165,rule_inst_5155,rule_inst_5160])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) r [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have absent : externExtract ctx T.ty_32_or_64 (.ty (.int (if half then 16 else 8))) st.base = .fail := by cases half <;> rfl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  have hp' := hp
  rcases member with rfl | rfl | rfl
  all_goals cases cc <;> cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,hp'.t2,hp'.t120,hp'.t2276,hp'.t2272,rule_inst_5165,rule_inst_5155,rule_inst_5160,sem_extract,sem_unData,
    sem_eq,sem_prim,stock_matchArgs,base_eq,base_prim,CTy.ofName?,ccIdx]
  all_goals rfl
private theorem narrow_wide_absurd {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y m : Nat} (typed : ctx.valueType? x = some (.int (if half then 16 else 8))) {r : Rule}
    (member : r ∈ [rule_inst_5165,rule_inst_5155,rule_inst_5160,rule_inst_5142])
    {st : State} {tr : Array RuleId} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (m+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals first
    | (rw [narrow128_failure hp ctx cc half typed st tr m] at matched; cases matched)
    | (rw [narrow_scalar_failure hp ctx cc half typed (by decide +kernel) st tr m] at matched; cases matched)
private theorem wide_failure {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8))) (wide128 : Bool)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if wide128 then rule_inst_5142 else rule_inst_5128)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have xTy := ext_value_type ctx st.base typeX
  have yTy := ext_value_type ctx st.base typeY
  have notWide : externExtract ctx T.ty_32_or_64 (.ty (.int (if half then 16 else 8))) st.base = .fail := by cases half <;> rfl
  have not128 : (V.ty (.int (if half then 16 else 8)) == V.ty (.int 128)) = false := by cases half <;> decide
  cases hp
  cases wide128 <;> cases half
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5142,rule_inst_5128,sem_extract,sem_unData,sem_eq,sem_prim,
    stock_matchArgs,base_eq,base_prim,CTy.ofName?]
private theorem cmp_internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
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

/-- Actual strict8/16 minmax emitters derive their canonical flags condition
and exactly one extension scratch without operand-classification premises. -/
theorem stock_minmax_narrow_emitter_shape {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (unsigned maximum half : Bool) {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int (if half then 16 else 8)))
    (typeY : ctx.valueType? y = some (.int (if half then 16 else 8))) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx (minmaxComparison unsigned maximum)) [],.value x,.value y]
      (st,tr) out (next,trace)) :
    ∃ mi,out = .data 123 2 [.data 47 1 [mi],.data 96 (condOf (minmaxComparison unsigned maximum)).idx []] ∧
      next.base.nextVreg = st.base.nextVreg+1 ∧ next.demand.size = st.demand.size := by
  let cc := minmaxComparison unsigned maximum
  have notEq : cc ≠ .eq := by cases unsigned <;> cases maximum <;> decide
  have notNe : cc ≠ .ne := by cases unsigned <;> cases maximum <;> decide
  have hp := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  change ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace) at run
  obtain ⟨pre,r,post,hL,hpre,matchN,rhsN,env,afterMatch,emittedState,rhsTrace,hm,he,stateEq,fuelEq⟩ :=
    cmp_internal_split_first hc hp.t652 term_652_kind rfl (by rw [hp.r652]; simp; omega) run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj stateEq
  subst fuel
  rw [hp.r652] at hL
  isel_rule_cases hL
  all_goals cases hp
  case inl.mk =>
    obtain ⟨_,_,_,equal,_⟩ := stock_cmp_zero_match_observed hp' ctx inv true false cc x y hm
    exact False.elim (notEq equal)
  case inr.inl.mk =>
    obtain ⟨_,_,_,equal,_⟩ := stock_cmp_zero_match_observed hp' ctx inv true true cc x y hm
    exact False.elim (notNe equal)
  case inr.inr.inl.mk =>
    obtain ⟨_,_,_,equal,_⟩ := stock_cmp_zero_match_observed hp' ctx inv false false cc x y hm
    exact False.elim (notEq equal)
  case inr.inr.inr.inl.mk =>
    obtain ⟨_,_,_,equal,_⟩ := stock_cmp_zero_match_observed hp' ctx inv false true cc x y hm
    exact False.elim (notNe equal)
  case inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (narrow_wide_absurd hp' ctx cc half typeX (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    have failed := wide_failure hp' ctx cc half typeX typeY false st tr matchN
    simp only [Bool.false_eq_true,ite_false] at failed
    rw [failed] at hm
    cases hm
  case inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    let ty : Clif.Ty := if half then .i16 else .i8
    have typed : ctx.valueType? x = some (.int ty.width) := by cases half <;> exact typeX
    obtain ⟨_,_,_,imm,_,_,_,_,_,envEq,stateEq⟩ :=
      stock_cmp_immediate_match_observed hp' ctx inv true cc ty x y typed hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20 = n+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at he
    have bits : ty.width = if half then 16 else 8 := by cases half <;> rfl
    rw [bits] at he
    obtain ⟨_,_,_,output,finish⟩ := stock_cmp_narrow_immediate_rhs_observed hp' ctx half cc typeX he
    exact ⟨_,output,(by rw [finish]; simp [LState.fresh,LState.emit]),(by rw [finish]; simp [State.mark])⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨_,envEq,stateEq⟩ := stock_cmp_narrow_match_observed hp' ctx cc half false typeY hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20 = n+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at he
    obtain ⟨_,_,_,_,_,_,output,finish⟩ := stock_cmp_narrow_rhs_observed hp' ctx false half cc typeX he
    exact ⟨_,output,(by rw [finish]; simp [LState.fresh,LState.emit]),(by rw [finish]; simp [State.mark])⟩
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.mk =>
    obtain ⟨_,envEq,stateEq⟩ := stock_cmp_narrow_match_observed hp' ctx cc half true typeY hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20 = n+160 := ⟨rhsN+20-160,by omega⟩
    rw [gas] at he
    obtain ⟨_,_,_,_,_,_,output,finish⟩ := stock_cmp_narrow_rhs_observed hp' ctx true half cc typeX he
    exact ⟨_,output,(by rw [finish]; simp [LState.fresh,LState.emit]),(by rw [finish]; simp [State.mark])⟩
end Backend.Stock.Proof.ScalarSelect

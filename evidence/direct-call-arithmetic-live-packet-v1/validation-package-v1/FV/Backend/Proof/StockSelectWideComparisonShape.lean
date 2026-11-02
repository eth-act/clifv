import FV.Backend.Proof.StockCmpRegisterEmission
import FV.Backend.Proof.StockCmpPredecessorSignedEmission
import FV.Backend.Proof.StockCmpMatchedRegister
import FV.Backend.Proof.StockCmpMatchedImmediate
import FV.Backend.Proof.StockCmpPredecessorUnsignedEmission
import FV.Backend.Proof.StockCmpMatchedPredecessor
import FV.Backend.Proof.StockCmpImmediateEmission
import FV.Backend.Proof.StockMinMaxRegisterRuns
import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockSelectZeroConditionShape
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
private theorem wide_incompatible {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (wide : Bool)
    {x y : Nat} (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32))) {r : Rule}
    (member : r ∈ [rule_inst_5142,rule_inst_5134,rule_inst_5117,rule_inst_5108])
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) r
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) : False := by
  have tx := ext_value_type ctx st.base typeX
  have ty := ext_value_type ctx st.base typeY
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals cases hp
  all_goals cases wide
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_inv [*,rule_inst_5142,rule_inst_5134,rule_inst_5117,rule_inst_5108,
    sem_extract,sem_unData,sem_eq,sem_prim,sem_ctor,base_eq,base_prim,ccIdx,CTy.ofName?] at matched
  all_goals isel_destruct <;> subst_vars
  all_goals simp only [typeX,typeY,Option.some.injEq,reduceCtorEq] at *
  all_goals isel_destruct <;> subst_vars
  all_goals simp [CTy.bits,CTy.ofName?,ext_fits_in_16_iff] at *
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

/-- Every successful actual32/64 comparison emitter derives a decoded
scalar condition under the original mapped context, for every operand form. -/
theorem stock_select_wide_comparison_condition_shape {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (cc : Clif.IntCC) (wide : Bool) {x y fuel : Nat}
    (typeX : ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : ctx.valueType? y = some (.int (if wide then 64 else 32))) (enough : 300 ≤ fuel)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 123 652
      [.data 145 (ccIdx cc) [],.value x,.value y] (st,tr) out (next,trace)) :
    CondShape out (fun _ => True) := by
  have hp := data_program
  have hp' := hp
  have hc : ({} : Config).checkOverlap = false := rfl
  obtain ⟨pre,r,post,hL,hpre,matchN,rhsN,env,afterMatch,emittedState,rhsTrace,hm,he,stateEq,fuelEq⟩ :=
    cmp_internal_split_first hc hp.t652 term_652_kind rfl (by rw [hp.r652]; simp; omega) run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj stateEq
  subst fuel
  rw [hp.r652] at hL
  isel_rule_cases hL
  all_goals cases hp
  case inl.mk =>
    obtain ⟨_,_,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_zero_match_observed hp' ctx inv true false cc x y hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact stock_select_zero_rhs_condition_shape (ty := if wide then .i64 else .i32) inv
      (by cases wide <;> simp [Clif.Ty.width]) true false
      (by cases wide <;> exact typeX) (by cases wide <;> exact typeY) he
  case inr.inl.mk =>
    obtain ⟨_,_,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_zero_match_observed hp' ctx inv true true cc x y hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact stock_select_zero_rhs_condition_shape (ty := if wide then .i64 else .i32) inv
      (by cases wide <;> simp [Clif.Ty.width]) true true
      (by cases wide <;> exact typeX) (by cases wide <;> exact typeY) he
  case inr.inr.inl.mk =>
    obtain ⟨_,_,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_zero_match_observed hp' ctx inv false false cc x y hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact stock_select_zero_rhs_condition_shape (ty := if wide then .i64 else .i32) inv
      (by cases wide <;> simp [Clif.Ty.width]) false false
      (by cases wide <;> exact typeX) (by cases wide <;> exact typeY) he
  case inr.inr.inr.inl.mk =>
    obtain ⟨_,_,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_zero_match_observed hp' ctx inv false true cc x y hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+240 := ⟨rhsN+20-240,by omega⟩
    rw [gas] at he
    exact stock_select_zero_rhs_condition_shape (ty := if wide then .i64 else .i32) inv
      (by cases wide <;> simp [Clif.Ty.width]) false true
      (by cases wide <;> exact typeX) (by cases wide <;> exact typeY) he
  case inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.mk =>
    exact False.elim (wide_incompatible hp' ctx cc wide typeX typeY (by decide +kernel) hm)
  case inr.inr.inr.inr.inl.mk =>
    let ty : Clif.Ty := if wide then .i64 else .i32
    have typed : ctx.valueType? x = some (.int ty.width) := by cases wide <;> exact typeX
    obtain ⟨_,_,_,imm,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_immediate_match_observed hp' ctx inv false cc ty x y typed hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    have bits : (if wide then OperandSize.size64 else .size32).bits = ty.width := by cases wide <;> rfl
    rw [← bits] at he
    obtain ⟨_,rx,mapped,output,_⟩ := stock_cmp_immediate_rhs_observed hp' ctx rfl cc
      (if wide then .size64 else .size32) he
    obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
    rw [output]
    refine Or.inr (Or.inr ⟨_,.aluRRImm12 .subS (if wide then .size64 else .size32) .xzr (.vreg key .int) imm,condOf cc,rfl,?_,(condOf_ne_al cc).1,(condOf_ne_al cc).2,(by cases wide <;> rfl),fun _ _ => trivial⟩)
    cases wide <;> rfl
  case inr.inr.inr.inr.inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨envEq,stateEq⟩ := stock_cmp_wide_match_observed hp' ctx cc
      (if wide then .size64 else .size32) (by cases wide <;> exact typeY) hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨_,_,rx,ry,mappedX,mappedY,output,_⟩ := stock_cmp_register_rhs_observed hp' ctx rfl cc
      (if wide then .size64 else .size32) he
    obtain ⟨kx,rfl⟩ := inv.valueReg x rx mappedX
    obtain ⟨ky,rfl⟩ := inv.valueReg y ry mappedY
    rw [output]
    refine Or.inr (Or.inr ⟨_,.aluRRR .subS (if wide then .size64 else .size32) .xzr (.vreg kx .int) (.vreg ky .int),condOf cc,rfl,?_,(condOf_ne_al cc).1,(condOf_ne_al cc).2,(by cases wide <;> rfl),fun _ _ => trivial⟩)
    cases wide <;> rfl
  case inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨_,_,_,imm,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_predecessor_match_observed hp' ctx inv false cc
      (if wide then .size64 else .size32) x y (by cases wide <;> exact typeX) hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨_,rx,mapped,output,_⟩ := stock_cmp_predecessor_unsigned_rhs_observed hp' ctx rfl
      (if wide then .size64 else .size32) he
    obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
    rw [output]
    refine Or.inr (Or.inr ⟨_,.aluRRImm12 .subS (if wide then .size64 else .size32) .xzr (.vreg key .int) imm,condOf .ugt,rfl,?_,(condOf_ne_al .ugt).1,(condOf_ne_al .ugt).2,(by cases wide <;> rfl),fun _ _ => trivial⟩)
    cases wide <;> rfl
  case inr.inr.inr.inr.inr.inr.inl.mk =>
    obtain ⟨_,_,_,imm,_,_,_,_,_,_,envEq,stateEq⟩ := stock_cmp_predecessor_match_observed hp' ctx inv true cc
      (if wide then .size64 else .size32) x y (by cases wide <;> exact typeX) hm
    rw [envEq,stateEq] at he
    obtain ⟨n,gas⟩ : ∃ n,rhsN+20=n+100 := ⟨rhsN+20-100,by omega⟩
    rw [gas] at he
    obtain ⟨_,rx,mapped,output,_⟩ := stock_cmp_predecessor_signed_rhs_observed hp' ctx rfl
      (if wide then .size64 else .size32) he
    obtain ⟨key,rfl⟩ := inv.valueReg x rx mapped
    rw [output]
    refine Or.inr (Or.inr ⟨_,.aluRRImm12 .subS (if wide then .size64 else .size32) .xzr (.vreg key .int) imm,condOf .sgt,rfl,?_,(condOf_ne_al .sgt).1,(condOf_ne_al .sgt).2,(by cases wide <;> rfl),fun _ _ => trivial⟩)
    cases wide <;> rfl
end Backend.Stock.Proof.ScalarSelect

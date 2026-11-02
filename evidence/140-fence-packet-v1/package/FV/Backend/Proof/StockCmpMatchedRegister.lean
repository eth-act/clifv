import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.IselTermsImm
import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselCtlTry
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
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
private def narrowRule (cc : Clif.IntCC) : Rule := if signedCC cc then rule_inst_5108 else rule_inst_5117
private def narrowEnv (cc : Clif.IntCC) (half : Bool) (x y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 1 (some (.value x))).setIfInBounds 3 (some (.value y))).setIfInBounds 2 (some (.ty (.int (if half then 16 else 8))))
private theorem narrowEnv_eq (cc : Clif.IntCC) (half : Bool) (x y : Nat) :
    narrowEnv cc half x y = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] := by
  apply Array.toList_inj.mp
  simp [narrowEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem signed_code (ctx : Ctx) (cc : Clif.IntCC) (st : State) :
    Stock.externCtor ctx T.signed_cond_code [.data 145 (ccIdx cc) []] st =
      if signedCC cc then .ok (.data 145 (ccIdx cc) [],st) else .fail := by
  rw [stock_ctor_baseOnly ctx T.signed_cond_code _ st (by decide)]
  cases cc <;> rfl
private theorem unsigned_code (ctx : Ctx) (cc : Clif.IntCC) (st : State) :
    Stock.externCtor ctx T.unsigned_cond_code [.data 145 (ccIdx cc) []] st =
      if signedCC cc then .fail else .ok (.data 145 (ccIdx cc) [],st) := by
  rw [stock_ctor_baseOnly ctx T.unsigned_cond_code _ st (by decide)]
  cases cc <;> rfl
private theorem narrow_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (narrowRule cc)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some (narrowEnv cc half x y),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have fits := ext_fits_in_16 ctx st.base (if half then 16 else 8)
  have signed := fun q => signed_code ctx cc q
  have unsigned := fun q => unsigned_code ctx cc q
  cases hp
  cases sign : signedCC cc <;> cases half
  all_goals simp only [narrowRule,sign,ite_true,ite_false,Bool.false_eq_true] at *
  all_goals isel_eval [*, isel_monad,narrowRule,narrowEnv,rule_inst_5108,rule_inst_5117,
    sem_extract,sem_unData,sem_eq,sem_ctor,stock_matchArgs]
private theorem opposite_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (half : Bool)
    {x y : Nat} (typed : ctx.valueType? y = some (.int (if half then 16 else 8)))
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+20) (if signedCC cc then rule_inst_5117 else rule_inst_5108)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (none,st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  have fits := ext_fits_in_16 ctx st.base (if half then 16 else 8)
  have signed := fun q => signed_code ctx cc q
  have unsigned := fun q => unsigned_code ctx cc q
  cases hp
  cases sign : signedCC cc <;> cases half
  all_goals simp only [narrowRule,sign,ite_true,ite_false,Bool.false_eq_true] at *
  all_goals isel_eval [*, isel_monad,rule_inst_5108,rule_inst_5117,
    sem_extract,sem_unData,sem_eq,sem_ctor,stock_matchArgs]
private def registerEnv (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Isle.Interp.Env V :=
  ((((Array.replicate 4 none).setIfInBounds 0 (some (.data 145 (ccIdx cc) []))).setIfInBounds 1 (some (.value x))).setIfInBounds 3 (some (.value y))).setIfInBounds 2 (some (.ty (.int sz.bits)))
private def RegisterMatches (p : Program) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) : Prop :=
  ∀ q trace n,(matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (q,trace) =
    .ok (some (registerEnv cc sz x y),q,trace)
attribute [local irreducible] RegisterMatches
private theorem registerEnv_eq (cc : Clif.IntCC) (sz : OperandSize) (x y : Nat) :
    registerEnv cc sz x y = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] := by
  apply Array.toList_inj.mp
  simp [registerEnv,Array.toList_setIfInBounds,List.set,List.replicate]
private theorem register_match {p : Program} (hp : Data p) (ctx : Ctx) (cc : Clif.IntCC) (sz : OperandSize)
    {x y : Nat} (typed : ctx.valueType? y = some (.int sz.bits)) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_inst_5128 [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) =
      .ok (some (registerEnv cc sz x y),st,tr) := by
  have lookup := ext_value_type ctx st.base typed
  cases hp
  cases sz
  all_goals isel_eval [*,rule_inst_5128,registerEnv,sem_extract,sem_unData,ext_ty_32_or_64_32,ext_ty_32_or_64_64,OperandSize.bits]
/-- Successful actual5128 matching derives the canonical original register
operands/type and leaves the complete scheduler state and trace unchanged. -/
theorem stock_cmp_wide_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (sz : OperandSize) {x y : Nat}
    (typed : ctx.valueType? y = some (.int sz.bits))
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) rule_inst_5128
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) :
    env = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] ∧
      after = (st,tr) := by
  have replay := register_match hp ctx cc sz (x := x) typed st tr (n+18)
  rw [show (n+18)+2=n+20 from by omega] at replay
  rw [replay] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  exact ⟨matched.1.symm.trans (registerEnv_eq cc sz x y),matched.2.symm⟩
/-- Actual5117/5108 matching derives signedness, both original operands,
canonical type/environment and complete state/trace preservation. -/
theorem stock_cmp_narrow_match_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (cc : Clif.IntCC) (half signed : Bool) {x y : Nat}
    (typed : ctx.valueType? y = some (.int (if half then 16 else 8)))
    {st : State} {tr : Array RuleId} {n : Nat} {env : Isle.Interp.Env V} {after : State × Array RuleId}
    (matched : (matchRule p (Stock.sem ctx) {} (n+20) (if signed then rule_inst_5108 else rule_inst_5117)
      [.data 145 (ccIdx cc) [],.value x,.value y]).run (st,tr) = .ok (some env,after)) :
    signedCC cc = signed ∧
      env = #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] ∧
      after = (st,tr) := by
  have main := narrow_match hp ctx cc half (x := x) typed st tr n
  have opposite := opposite_match hp ctx cc half (x := x) typed st tr n
  cases signed <;> cases sign : signedCC cc
  all_goals simp only [narrowRule,sign,Bool.false_eq_true,ite_true,ite_false] at main opposite matched ⊢
  all_goals first
    | (rw [opposite] at matched; cases matched)
    | (rw [main] at matched
       simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
       exact ⟨True.intro,matched.1.symm.trans (narrowEnv_eq cc half x y),matched.2.symm⟩)
end Backend.Stock.Proof.ScalarCmp

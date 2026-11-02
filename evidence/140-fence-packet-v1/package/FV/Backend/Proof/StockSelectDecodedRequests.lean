import FV.Backend.Proof.StockSelectDecodeFlags
import FV.Backend.Proof.StockSelectRequests
namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- An actual successful select RHS derives the producer decoder internally. -/
theorem stock_select_rhs_producer_decoded {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {st next : State} {tr trace : Array RuleId}
    {n w x y : Nat} {mi out : V} (condition : Cond)
    (run : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi (.data 96 condition.idx []))).run (st,tr) = .ok (some out,next,trace)) :
    ∃ m,MInst.ofV mi = some m := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY⟩ := stock_select_rhs_requests hp ctx run
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mapY safeY
  have get0 : (selectEnv w x y mi (.data 96 condition.idx []))[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (selectEnv w x y mi (.data 96 condition.idx []))[1]? = some (some (.data 47 1 [mi])) := rfl
  have get2 : (selectEnv w x y mi (.data 96 condition.idx []))[2]? = some (some (.data 96 condition.idx [])) := rfl
  have get3 : (selectEnv w x y mi (.data 96 condition.idx []))[3]? = some (some (.value x)) := rfl
  have get4 : (selectEnv w x y mi (.data 96 condition.idx []))[4]? = some (some (.value y)) := rfl
  have saved := hp
  cases hp
  isel_inv [*,rule_inst_5364,sem_ctor,sem_mkData] at run
  simp only [stock_put_in_reg_iff,mapX,mapY,Option.some.injEq] at *
  isel_destruct
  subst_vars
  rename_i consumer built flagCall _ _ _ actualX actualY _ _ _ builtCall _ _
  have replay := stock_csel_builder saved ctx hc ((st.mark x).mark y) tr (n+76)
    (.data 96 condition.idx []) (.reg actualX) (.reg actualY)
  unfold ApplyInternal at builtCall
  rw [builtCall] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  obtain ⟨rfl,rfl⟩ := replay
  obtain ⟨m1,m2,decoded,_,_,_⟩ := stock_select_with_flags_decoded saved ctx hc (by omega) flagCall
  exact ⟨m1,decoded⟩
end Backend.Stock.Proof.ScalarSelect

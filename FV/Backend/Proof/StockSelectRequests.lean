module

public import FV.Backend.Proof.StockSelectBuilders
public import FV.Backend.Proof.StockRequestSuccess

@[expose] public section

namespace Backend.Stock.Proof.ScalarSelect
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Canonical scalar select environment obtained from actual matching. -/
def selectEnv (w x y : Nat) (mi condition : V) : Isle.Interp.Env V :=
  #[some (.ty (.int w)),some (.data 47 1 [mi]),some condition,some (.value x),some (.value y)]
/-- Successful real scalar select RHS supplies both demand guards and source
register mappings internally. This lemma carries no separately assumed requests. -/
theorem stock_select_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {st next : State} {tr trace : Array RuleId} {n w x y : Nat} {mi condition out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi condition)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  have get0 : (selectEnv w x y mi condition)[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (selectEnv w x y mi condition)[1]? = some (some (.data 47 1 [mi])) := rfl
  have get2 : (selectEnv w x y mi condition)[2]? = some (some (condition)) := rfl
  have get3 : (selectEnv w x y mi condition)[3]? = some (some (.value x)) := rfl
  have get4 : (selectEnv w x y mi condition)[4]? = some (some (.value y)) := rfl
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi condition)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5364,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi condition)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5364,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx,sx⟩ := result
    obtain ⟨safeX,rx,mapX,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
        (selectEnv w x y mi condition)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_5364,sem_ctor,sem_mkData]
        intro impossible; cases impossible
      exact False.elim (denied run)
    | unmodeled e =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
        (selectEnv w x y mi condition)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_5364,sem_ctor,sem_mkData]
        intro impossible; cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨vy,sy⟩ := result
      obtain ⟨safeY,ry,mapY,_,_⟩ := (stock_put_in_reg_iff ctx (st.mark x) y vy sy).mp yCall
      exact ⟨safeX,safeY,rx,ry,mapX,mapY⟩
/-- Replay the real scalar select RHS with the guarded requests; all scheduling
fields and both emitted instructions are recorded exactly. -/
theorem stock_select_rhs_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (w : Nat) (st : State) (tr : Array RuleId) (n : Nat) (condition : Cond)
    {x y : Nat} {mi : V} {m : MInst} (decoded : MInst.ofV mi = some m) {rx ry : Reg}
    (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi (.data 96 condition.idx []))).run (st,tr) =
      .ok (some (.regs [(st.base.fresh .int).1]),
        {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))},
        (tr.push rule_inst_3059.id).push rule_prelude_lower_818.id) := by
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mapY safeY
  have builder := fun q trace fuel => stock_csel_builder hp ctx hc q trace fuel
    (.data 96 condition.idx []) (.reg rx) (.reg ry)
  have decodedSelect : MInst.ofV (.data 58 31 [.reg (st.base.fresh .int).1,
      .data 96 condition.idx [],.reg rx,.reg ry]) =
      some (.csel (st.base.fresh .int).1 rx ry condition) := by
    rw [ofV_csel',V.cond?_data,cond_ofIdx_idx]
    rfl
  have flags := fun q trace fuel => ScalarCmp.stock_cmp_with_flags_reg hp ctx hc q trace fuel
    decoded decodedSelect (st.base.fresh .int).1
  have get0 : (selectEnv w x y mi (.data 96 condition.idx []))[0]? = some (some (.ty (.int w))) := rfl
  have get1 : (selectEnv w x y mi (.data 96 condition.idx []))[1]? = some (some (.data 47 1 [mi])) := rfl
  have get2 : (selectEnv w x y mi (.data 96 condition.idx []))[2]? = some (some (.data 96 condition.idx [])) := rfl
  have get3 : (selectEnv w x y mi (.data 96 condition.idx []))[3]? = some (some (.value x)) := rfl
  have get4 : (selectEnv w x y mi (.data 96 condition.idx []))[4]? = some (some (.value y)) := rfl
  simp only [State.mark] at requestX requestY builder flags ⊢
  cases hp
  isel_eval [*,rule_inst_5364,sem_ctor,sem_mkData]
  all_goals rfl
/-- Complete output and full scheduling state of a successful actual scalar
select RHS, with the operand request premises derived internally. -/
theorem stock_select_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {st next : State} {tr trace : Array RuleId}
    {n w x y : Nat} {mi out : V} {m : MInst} (condition : Cond) (decoded : MInst.ofV mi = some m)
    (run : (evalExpr p (Stock.sem ctx) cfg (n+120) rule_inst_5364.rhs
      (selectEnv w x y mi (.data 96 condition.idx []))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .regs [(st.base.fresh .int).1] ∧
        next = {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))} := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY⟩ := stock_select_rhs_requests hp ctx run
  have replay := stock_select_rhs_run hp ctx hc w st tr n condition decoded mapX mapY safeX safeY
  rw [run] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  exact ⟨safeX,safeY,rx,ry,mapX,mapY,replay.1,replay.2.1⟩
end Backend.Stock.Proof.ScalarSelect

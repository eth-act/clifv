import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockSelectBuilders
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
/-- Actual select of an explicit flag condition emits the original producer and
one csel; source marks and all other scheduling fields are retained exactly. -/
theorem stock_select_flags_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w x y : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (st : State) (tr : Array RuleId) (n : Nat) (condition : Cond)
    {mi : V} {m : MInst} (decoded : MInst.ofV mi = some m) {rx ry : Reg}
    (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    (applyTerm p (Stock.sem ctx) cfg (n+220) 22 659
      [.ty (.int w),.data 123 2 [.data 47 1 [mi],.data 96 condition.idx []],.value x,.value y]).run (st,tr) =
      .ok (some (.regs [(st.base.fresh .int).1]),
        {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit m).emit
          (.csel (st.base.fresh .int).1 rx ry condition))},
        (((tr.push rule_inst_3059.id).push rule_prelude_lower_818.id).push rule_inst_5364.id).push rule_inst_5324.id) := by
  have consumer := fun fuel => stock_select_cond_run hp ctx hc width st tr fuel condition decoded mapX mapY safeX safeY
  cases hp
  isel_eval [*,rule_inst_5320,rule_inst_5322,rule_inst_5324,rule_inst_5331,sem_ctor,sem_unData,stock_matchArgs]
/-- Actual Zero/NotZero select uses the register-zero comparison and csel,
retaining the original condition size and complete guarded scheduling state. -/
theorem stock_select_zero_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w x y : Nat} (width : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (st : State) (tr : Array RuleId) (n : Nat) (nonzero : Bool) (size : OperandSize) (key : Nat)
    {rx ry : Reg} (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    (applyTerm p (Stock.sem ctx) cfg (n+220) 22 659
      [.ty (.int w),.data 123 (if nonzero then 1 else 0)
        [.reg (.vreg key .int),.data 93 (if size = .size32 then 0 else 1) []],.value x,.value y]).run (st,tr) =
      .ok (some (.regs [(st.base.fresh .int).1]),
        {(st.mark x).mark y with base := (((st.base.fresh .int).2.emit (cmpXzr size key)).emit
          (.csel (st.base.fresh .int).1 rx ry (if nonzero then .ne else .eq)))},
        ((((tr.push rule_inst_2767.id).push rule_inst_3059.id).push rule_prelude_lower_818.id).push rule_inst_5364.id).push
          (if nonzero then rule_inst_5322.id else rule_inst_5320.id)) := by
  have builder := fun q trace fuel => ScalarCmp.stock_cmp_rr_builder hp ctx hc q trace fuel
    (.data 93 (if size = .size32 then 0 else 1) []) (.reg (.vreg key .int)) (.reg .xzr)
  have decoded : MInst.ofV (.data 58 2 [.data 59 10 [],.data 93 (if size = .size32 then 0 else 1) [],
      .reg .xzr,.reg (.vreg key .int),.reg .xzr]) = some (cmpXzr size key) := by cases size <;> rfl
  have consumer := fun fuel => stock_select_cond_run hp ctx hc width st (tr.push rule_inst_2767.id) fuel
    (if nonzero then .ne else .eq) decoded mapX mapY safeX safeY
  have register := fun q => zero ctx q
  cases hp
  cases nonzero
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals simp only [Cond.idx] at consumer
  all_goals isel_eval [*,rule_inst_5320,rule_inst_5322,rule_inst_5324,rule_inst_5331,sem_ctor,sem_mkData,sem_unData,stock_matchArgs]
end Backend.Stock.Proof.ScalarSelect

import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockCmpPure
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : LState) :
    (Backend.sem ctx).ctor t vs st = Backend.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Backend.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_prim (ctx : Ctx) : (Backend.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
/-- Actual Stock register comparison construction preserves all scheduling fields. -/
theorem stock_cmp_rr_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (sz rx ry : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 47 390 [sz,rx,ry]).run (st,tr) =
      .ok (some (.data 47 1 [.data 58 2 [.data 59 10 [],sz,.reg .xzr,rx,ry]]),st,tr.push rule_inst_2767.id) := by
  have legacy : (applyTerm p (Backend.sem ctx) cfg (n+40) 47 390 [sz,rx,ry]).run (st.base,tr) =
      .ok (some (.data 47 1 [.data 58 2 [.data 59 10 [],sz,.reg .xzr,rx,ry]]),st.base,tr.push rule_inst_2767.id) := by
    cases hp
    isel_eval [*,rule_inst_2767,sem_ctor,sem_mkData,sem_prim,ctor_writable_zero_reg,ctor_writable_reg_to_reg,ctor_temp_writable_reg_i64]
  simpa only using stock_cmp_pure_helper hp ctx hc (by decide) legacy
/-- Actual Stock immediate comparison construction preserves all scheduling fields. -/
theorem stock_cmp_imm_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (sz rx immediate : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 47 391 [sz,rx,immediate]).run (st,tr) =
      .ok (some (.data 47 1 [.data 58 4 [.data 59 10 [],sz,.reg .xzr,rx,immediate]]),st,tr.push rule_inst_2774.id) := by
  have legacy : (applyTerm p (Backend.sem ctx) cfg (n+40) 47 391 [sz,rx,immediate]).run (st.base,tr) =
      .ok (some (.data 47 1 [.data 58 4 [.data 59 10 [],sz,.reg .xzr,rx,immediate]]),st.base,tr.push rule_inst_2774.id) := by
    cases hp
    isel_eval [*,rule_inst_2774,sem_ctor,sem_mkData,sem_prim,ctor_writable_zero_reg,ctor_writable_reg_to_reg,ctor_temp_writable_reg_i64]
  simpa only using stock_cmp_pure_helper hp ctx hc (by decide) legacy
/-- Actual Stock conditional-set construction allocates exactly its fresh result
and retains the original scheduling fields. -/
theorem stock_cmp_cset_builder {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (condition : V) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 49 426 [condition]).run (st,tr) =
      .ok (some (.data 49 3 [.data 58 33 [.reg (st.base.fresh .int).1,condition],.reg (st.base.fresh .int).1]),
        {st with base := (st.base.fresh .int).2},tr.push rule_inst_3068.id) := by
  have legacy : (applyTerm p (Backend.sem ctx) cfg (n+40) 49 426 [condition]).run (st.base,tr) =
      .ok (some (.data 49 3 [.data 58 33 [.reg (st.base.fresh .int).1,condition],.reg (st.base.fresh .int).1]),
        (st.base.fresh .int).2,tr.push rule_inst_3068.id) := by
    cases hp
    isel_eval [*,rule_inst_3068,sem_ctor,sem_mkData,sem_prim,ctor_writable_zero_reg,ctor_writable_reg_to_reg,ctor_temp_writable_reg_i64]
  exact stock_cmp_pure_helper hp ctx hc (by decide) legacy
end Backend.Stock.Proof.ScalarCmp

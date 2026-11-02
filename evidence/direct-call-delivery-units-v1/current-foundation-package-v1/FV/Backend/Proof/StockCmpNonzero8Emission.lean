import FV.Backend.Proof.IselCmpIcmp
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockCmpTestBuilder
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I32" = some (.ty (.int 32)) := rfl
section Integers
attribute [local semireducible] Isle.Aarch64.program
private theorem mask (ctx : Ctx) : (Stock.sem ctx).int 4 255 = .int 255 := rfl
end Integers
private theorem immediate (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.u64_into_imm_logic [.ty (.int 32),.int 255] st =
      .ok (.op (.immLogic ⟨255,.size32⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.u64_into_imm_logic _ st (by decide)]
  have call := (ctor_u64_into_imm_logic_255 ctx st.base (.op (.immLogic ⟨255,.size32⟩)) st.base).mpr ⟨rfl,rfl⟩
  rw [call]
/-- Actual8-bit nonzero RHS requests its guarded source and constructs the exact
masked flag producer while preserving every other Stock scheduling field. -/
theorem stock_cmp_nonzero8_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (x : Nat) (rx : Reg) (st : State) (tr : Array RuleId) (n : Nat)
    (mapped : ctx.valueReg? x = some rx) (safe : DemandAllowed ctx st x) :
    (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_4988.rhs #[some (.value x)]).run (st,tr) =
      .ok (some (.data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],
        .reg .xzr,.reg rx,.op (.immLogic ⟨255,.size32⟩)]],.data 96 1 []]),
        st.mark x,(tr.push rule_inst_1592.id).push rule_inst_3044.id) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have literal := fun q => immediate ctx q
  have builder := fun q trace fuel => stock_cmp_test32_builder hp ctx hc q trace fuel
    (.reg rx) (.op (.immLogic ⟨255,.size32⟩))
  have get : (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) := rfl
  cases hp
  isel_eval [*,rule_inst_4988,sem_ctor,sem_mkData,sem_prim,mask]
/-- A successful real8-bit nonzero RHS supplies its original demand guard,
mapped register, exact condition and full marked state internally. -/
theorem stock_cmp_nonzero8_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_4988.rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
      out = .data 123 2 [.data 47 1 [.data 58 5 [.data 59 5 [],.data 93 0 [],.reg .xzr,.reg rx,.op (.immLogic ⟨255,.size32⟩)]],.data 96 1 []] ∧ next = st.mark x := by
  have get : (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) := rfl
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_4988.rhs #[some (.value x)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_4988,sem_ctor,sem_mkData,sem_prim,mask]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_4988.rhs #[some (.value x)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_4988,sem_ctor,sem_mkData,sem_prim,mask]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x value after).mp request
    have replay := stock_cmp_nonzero8_rhs hp ctx hc x rx st tr n mapped safe
    rw [run] at replay
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
    exact ⟨safe,rx,mapped,replay.1,replay.2.1⟩
end Backend.Stock.Proof.ScalarCmp

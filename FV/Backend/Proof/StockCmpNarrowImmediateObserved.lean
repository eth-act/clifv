import FV.Backend.Proof.StockExtendRequests
import FV.Backend.Proof.StockCmpNarrowImmediateRhs
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Actual5134 RHS success derives its guarded source request and mapping
through the real zero-extension helper. -/
theorem stock_cmp_narrow_immediate_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (half : Bool) (cc : Clif.IntCC) {x : Nat} {imm : Imm12}
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+160) rule_inst_5134.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),
        some (.value x),some (.op (.imm12 imm))]).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[1]? = some (some (.ty (.int (if half then 16 else 8)))) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[2]? = some (some (.value x)) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),some (.value x),some (.op (.imm12 imm))] : Isle.Interp.Env V)[3]? = some (some (.op (.imm12 imm))) := rfl
  have hp' := hp
  cases hp
  isel_inv [*,rule_inst_5134,sem_ctor,sem_mkData,Array.getElem?_eq_getElem] at run
  all_goals isel_destruct <;> subst_vars
  have shape := ScalarShift.stock_zext32_out hp' (cfg := {}) (n := n+153) rfl (by omega) (by assumption)
  obtain ⟨t,typed,safe,rx,mapped,form⟩ := shape
  exact ⟨safe,rx,mapped⟩
/-- Original narrow typing and successful5134 execution derive the exact
immediate producer, one extension allocation and complete marked Stock state. -/
theorem stock_cmp_narrow_immediate_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (half : Bool) (cc : Clif.IntCC) {x : Nat} {imm : Imm12}
    (type : ctx.valueType? x = some (.int (if half then 16 else 8)))
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+160) rule_inst_5134.rhs
      #[some (.data 145 (ccIdx cc) []),some (.ty (.int (if half then 16 else 8))),
        some (.value x),some (.op (.imm12 imm))]).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
      out = .data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [],.data 93 0 [],.reg .xzr,
        .reg (st.base.fresh .int).1,.op (.imm12 imm)]],.data 96 (condOf cc).idx []] ∧
      next = {st.mark x with base := ((st.base.fresh .int).2.emit
        (.extend (st.base.fresh .int).1 rx false (if half then 16 else 8) 32))} := by
  obtain ⟨safe,rx,mapped⟩ := stock_cmp_narrow_immediate_rhs_requests hp ctx half cc run
  obtain ⟨rhsTrace,replay⟩ := stock_cmp_narrow_immediate_rhs hp ctx half cc imm type mapped st safe tr n
  rw [run] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  exact ⟨safe,rx,mapped,replay.1,replay.2.1⟩
end Backend.Stock.Proof.ScalarCmp

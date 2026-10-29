module

public import FV.Backend.Proof.StockCmpNarrowRhs
public import FV.Backend.Proof.StockExtendRequests

@[expose] public section

namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
/-- Successful narrow comparison RHS execution supplies both original source
request guards and mapped registers, without caller request certificates. -/
theorem stock_cmp_narrow_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (signed half : Bool) (cc : Clif.IntCC) {x y : Nat}
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+160)
      (if signed then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),
        some (.ty (.int (if half then 16 else 8))),some (.value y)]).run (st,tr) =
      .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[2]? = some (some (.ty (.int (if half then 16 else 8)))) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int (if half then 16 else 8))),some (.value y)] : Isle.Interp.Env V)[3]? = some (some (.value y)) := rfl
  have hp' := hp
  cases signed
  · simp only [Bool.false_eq_true,ite_false] at run
    cases hp
    isel_inv [*,rule_inst_5117,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,stock_put_in_reg_iff] at run
    all_goals isel_destruct <;> subst_vars
    all_goals try simp only [stock_put_in_reg_iff] at *
    all_goals isel_destruct <;> subst_vars
    rename_i producer condition vx final builderState extension opState leftState condCall leftCall guard ry mapY builderCall opCall
    have mappedY : ∃ ry,ctx.valueReg? y = some ry := ⟨ry,mapY⟩
    have shape := ScalarShift.stock_zext32_out hp' (cfg := {}) (n := n+153) rfl (by omega) leftCall
    obtain ⟨t,typed,safeX,rx,mapX,form⟩ := shape
    rcases form with ⟨_,_,finish⟩ | ⟨_,_,_,finish⟩
    all_goals rw [finish] at guard
    all_goals exact ⟨safeX,guard,⟨rx,mapX⟩,mappedY⟩
  · simp only [ite_true] at run
    cases hp
    isel_inv [*,rule_inst_5108,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,stock_put_in_reg_iff] at run
    all_goals isel_destruct <;> subst_vars
    all_goals try simp only [stock_put_in_reg_iff] at *
    all_goals isel_destruct <;> subst_vars
    rename_i producer condition vx final builderState extension opState leftState condCall leftCall guard ry mapY builderCall opCall
    have mappedY : ∃ ry,ctx.valueReg? y = some ry := ⟨ry,mapY⟩
    have shape := ScalarShift.stock_sext32_out hp' (cfg := {}) (n := n+153) rfl (by omega) leftCall
    obtain ⟨t,typed,safeX,rx,mapX,form⟩ := shape
    rcases form with ⟨_,_,finish⟩ | ⟨_,_,_,finish⟩
    all_goals rw [finish] at guard
    all_goals exact ⟨safeX,guard,⟨rx,mapX⟩,mappedY⟩
/-- Successful actual narrow RHS execution derives its exact producer and
complete extension/marking state from original source typing. -/
theorem stock_cmp_narrow_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    (signed half : Bool) (cc : Clif.IntCC) {x y : Nat}
    (type : ctx.valueType? x = some (.int (if half then 16 else 8)))
    {st next : State} {tr trace : Array RuleId} {n : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+160)
      (if signed then rule_inst_5108 else rule_inst_5117).rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),
        some (.ty (.int (if half then 16 else 8))),some (.value y)]).run (st,tr) =
      .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .data 123 2 [.data 47 1 [.data 58 8 [.data 59 10 [],.data 93 0 [],.reg .xzr,
          .reg (st.base.fresh .int).1,.reg ry,
          .data 84 (if signed then (if half then 5 else 4) else (if half then 1 else 0)) []]],
          .data 96 (condOf cc).idx []] ∧
        next = {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
          (.extend (st.base.fresh .int).1 rx signed (if half then 16 else 8) 32))} := by
  obtain ⟨safeX,safeY,rx,ry,mapX,mapY⟩ := stock_cmp_narrow_rhs_requests hp ctx signed half cc run
  obtain ⟨rhsTrace,replay⟩ := stock_cmp_narrow_rhs hp ctx signed half cc type mapX mapY st safeX safeY tr n
  rw [run] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  exact ⟨safeX,safeY,rx,ry,mapX,mapY,replay.1,replay.2.1⟩
end Backend.Stock.Proof.ScalarCmp

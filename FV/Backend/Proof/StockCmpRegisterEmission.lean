import FV.Backend.Proof.IselCmpEmit
import FV.Backend.Proof.StockCmpBuilders
import FV.Backend.Proof.StockDivPure
import FV.Backend.Proof.StockRequestSuccess
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem condition (ctx : Ctx) (st : State) (cc : Clif.IntCC) :
    Stock.externCtor ctx T.cond_code [.data 145 (ccIdx cc) []] st =
      .ok (.data 96 (condOf cc).idx [],st) := by
  rw [stock_ctor_baseOnly ctx T.cond_code _ st (by decide)]
  have legacy := (ctor_cond_code_iff ctx st.base (.data 145 (ccIdx cc) [])
    (.data 96 (condOf cc).idx []) st.base).mpr
    ⟨condOf cc,by rw [V.intcc?_data]; exact some_bind_ccIdx cc,rfl,rfl⟩
  exact congrArg (fun r => match r with
    | .ok (v,base) => ExtResult.ok (v,{st with base})
    | .fail => .fail | .unmodeled e => .unmodeled e) legacy
/-- The real register-comparison emitter RHS performs both guarded source
requests, builds its exact flag producer, and preserves every other Stock field. -/
theorem stock_cmp_register_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (cc : Clif.IntCC) (sz : OperandSize)
    (st : State) (tr : Array RuleId) (n x y : Nat) (rx ry : Reg)
    (mappedX : ctx.valueReg? x = some rx) (mappedY : ctx.valueReg? y = some ry)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx (st.mark x) y) :
    (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) = .ok (some (.data 123 2
        [.data 47 1 [.data 58 2 [.data 59 10 [],.data 93 (if sz = .size32 then 0 else 1) [],
          .reg .xzr,.reg rx,.reg ry]],.data 96 (condOf cc).idx []]),
        (st.mark x).mark y,
        (tr.push (if sz = .size32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2767.id) := by
  have requestX := stock_put_in_reg ctx st x rx mappedX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mappedY safeY
  have builder := fun q trace fuel => stock_cmp_rr_builder hp ctx hc q trace fuel
    (.data 93 (if sz = .size32 then 0 else 1) []) (.reg rx) (.reg ry)
  have code := fun q => condition ctx q cc
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[2]? = some (some (.ty (.int sz.bits))) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[3]? = some (some (.value y)) := rfl
  cases sz
  · simp only [ite_true] at builder
    simp only [OperandSize.bits] at get0 get1 get2 get3
    have size := fun (q : State) (trace : Array RuleId) (fuel : Nat) => ScalarDiv.stock_div_pure_helper hp ctx hc (st := q) (t := 305) (by decide)
      (operand_size_32 hp ctx hc q.base trace fuel (w := 32) (by decide))
    cases hp
    isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,OperandSize.bits,reduceCtorEq]
  · simp only [reduceCtorEq,ite_false] at builder
    simp only [OperandSize.bits] at get0 get1 get2 get3
    have size := fun (q : State) (trace : Array RuleId) (fuel : Nat) => ScalarDiv.stock_div_pure_helper hp ctx hc (st := q) (t := 305) (by decide)
      (operand_size_64 hp ctx hc q.base trace fuel (w := 64) (by decide) (by decide))
    cases hp
    isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,OperandSize.bits,reduceCtorEq]
private theorem size_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (sz : OperandSize) (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+8) 93 305 [.ty (.int sz.bits)]).run (st,tr) =
      .ok (some (.data 93 (if sz = .size32 then 0 else 1) []),st,
        tr.push (if sz = .size32 then rule_inst_1592.id else rule_inst_1593.id)) := by
  cases sz
  · exact ScalarDiv.stock_div_pure_helper hp ctx hc (st := st) (t := 305) (by decide)
      (operand_size_32 hp ctx hc st.base tr n (w := 32) (by decide))
  · exact ScalarDiv.stock_div_pure_helper hp ctx hc (st := st) (t := 305) (by decide)
      (operand_size_64 hp ctx hc st.base tr n (w := 64) (by decide) (by decide))
/-- Success of the actual register-emitter RHS supplies both guarded original
source requests and mapped registers; callers need no request certificates. -/
theorem stock_cmp_register_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (cc : Clif.IntCC) (sz : OperandSize)
    {st next : State} {tr trace : Array RuleId} {n x y : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  have size := fun q trace fuel => size_run hp ctx hc sz q trace fuel
  have get0 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[0]? = some (some (.data 145 (ccIdx cc) [])) := rfl
  have get1 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[2]? = some (some (.ty (.int sz.bits))) := rfl
  have get3 : (#[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)] : Isle.Interp.Env V)[3]? = some (some (.value y)) := rfl
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx,sx⟩ := result
    obtain ⟨safeX,rx,mappedX,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
        #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData]
        intro impossible; cases impossible
      exact False.elim (denied run)
    | unmodeled e =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
        #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_5128,sem_ctor,sem_mkData]
        intro impossible; cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨vy,sy⟩ := result
      obtain ⟨safeY,ry,mappedY,_,_⟩ := (stock_put_in_reg_iff ctx (st.mark x) y vy sy).mp yCall
      exact ⟨safeX,safeY,rx,ry,mappedX,mappedY⟩
/-- The exact producer and complete marked state follow from real successful
RHS execution, with all source guards and register mappings derived internally. -/
theorem stock_cmp_register_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (cc : Clif.IntCC) (sz : OperandSize)
    {st next : State} {tr trace : Array RuleId} {n x y : Nat} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value x),some (.ty (.int sz.bits)),some (.value y)]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx (st.mark x) y ∧
      ∃ rx ry,ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
        out = .data 123 2 [.data 47 1 [.data 58 2 [.data 59 10 [],
          .data 93 (if sz = .size32 then 0 else 1) [],.reg .xzr,.reg rx,.reg ry]],
          .data 96 (condOf cc).idx []] ∧ next = (st.mark x).mark y := by
  obtain ⟨safeX,safeY,rx,ry,mappedX,mappedY⟩ := stock_cmp_register_rhs_requests hp ctx hc cc sz run
  have replay := stock_cmp_register_rhs hp ctx hc cc sz st tr n x y rx ry mappedX mappedY safeX safeY
  rw [run] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  exact ⟨safeX,safeY,rx,ry,mappedX,mappedY,replay.1,replay.2.1⟩
private def fixtureCtx : Ctx := {sinkCtx with
  valDef := #[none,none]
  valReg := #[some (.vreg 1 .int),some (.vreg 3 .int)]}
/-- Both machine widths and every integer condition inhabit the real guarded
emitter RHS, including distinct mapped operands and both demand marks. -/
theorem stock_cmp_register_rhs_witness (sz : OperandSize) (cc : Clif.IntCC) :
    ∃ out trace,(evalExpr program (Stock.sem fixtureCtx) {} 1000 rule_inst_5128.rhs
      #[some (.data 145 (ccIdx cc) []),some (.value 0),some (.ty (.int sz.bits)),some (.value 1)]).run
      (sinkState,#[]) = .ok (some out,(sinkState.mark 0).mark 1,trace) ∧
      CondShape out (fun _ => True) := by
  have safe0 : DemandAllowed fixtureCtx sinkState 0 := by
    intro i impossible
    change none = some i at impossible
    cases impossible
  have safe1 : DemandAllowed fixtureCtx (sinkState.mark 0) 1 := by
    intro i impossible
    change none = some i at impossible
    cases impossible
  have actual := stock_cmp_register_rhs data_program fixtureCtx (cfg := {}) rfl cc sz sinkState #[] 900 0 1
    (.vreg 1 .int) (.vreg 3 .int) rfl rfl safe0 safe1
  refine ⟨_,_,actual,Or.inr (Or.inr ⟨_,
    MInst.aluRRR .subS sz .xzr (.vreg 1 .int) (.vreg 3 .int),condOf cc,rfl,?_,
    (condOf_ne_al cc).1,(condOf_ne_al cc).2,rfl,fun _ _ => trivial⟩)⟩
  cases sz <;> rfl
end Backend.Stock.Proof.ScalarCmp

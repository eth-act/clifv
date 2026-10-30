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
/-- The real immediate-comparison emitter RHS performs its guarded source request,
builds its exact immediate flag producer, and preserves all other Stock fields. -/
theorem stock_cmp_predecessor_unsigned_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (sz : OperandSize)
    (st : State) (tr : Array RuleId) (n x : Nat) (literal : Int) (rx : Reg) (imm : Imm12)
    (mappedX : ctx.valueReg? x = some rx) (safeX : DemandAllowed ctx st x) :
    (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some (.data 123 2
        [.data 47 1 [.data 58 4 [.data 59 10 [],.data 93 (if sz = .size32 then 0 else 1) [],
          .reg .xzr,.reg rx,.op (.imm12 imm)]],.data 96 (condOf .ugt).idx []]),
        st.mark x,
        (tr.push (if sz = .size32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2774.id) := by
  have requestX := stock_put_in_reg ctx st x rx mappedX safeX
  have builder := fun q trace fuel => stock_cmp_imm_builder hp ctx hc q trace fuel
    (.data 93 (if sz = .size32 then 0 else 1) []) (.reg rx) (.op (.imm12 imm))
  have get0 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[0]? = some (some (.ty (.int sz.bits))) := rfl
  have get1 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[2]? = some (some (.int literal)) := rfl
  have get3 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[3]? = some (some (.op (.imm12 imm))) := rfl
  cases sz
  · simp only [ite_true] at builder
    simp only [OperandSize.bits] at get0 get1 get2 get3
    have size := fun (q : State) (trace : Array RuleId) (fuel : Nat) => ScalarDiv.stock_div_pure_helper hp ctx hc (st := q) (t := 305) (by decide)
      (operand_size_32 hp ctx hc q.base trace fuel (w := 32) (by decide))
    cases hp
    isel_eval [*,rule_inst_5155,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,OperandSize.bits,reduceCtorEq]
    rfl
  · simp only [reduceCtorEq,ite_false] at builder
    simp only [OperandSize.bits] at get0 get1 get2 get3
    have size := fun (q : State) (trace : Array RuleId) (fuel : Nat) => ScalarDiv.stock_div_pure_helper hp ctx hc (st := q) (t := 305) (by decide)
      (operand_size_64 hp ctx hc q.base trace fuel (w := 64) (by decide) (by decide))
    cases hp
    isel_eval [*,rule_inst_5155,sem_ctor,sem_mkData,Array.getElem?_eq_getElem,OperandSize.bits,reduceCtorEq]
    rfl
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
/-- Success of the actual register-emitter RHS supplies the guarded original
source request and mapped register; callers need no request certificates. -/
theorem stock_cmp_predecessor_unsigned_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (sz : OperandSize)
    {st next : State} {tr trace : Array RuleId} {n x : Nat} {literal : Int} {imm : Imm12} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  have size := fun q trace fuel => size_run hp ctx hc sz q trace fuel
  have get0 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[0]? = some (some (.ty (.int sz.bits))) := rfl
  have get1 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[1]? = some (some (.value x)) := rfl
  have get2 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[2]? = some (some (.int literal)) := rfl
  have get3 : (#[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))] : Isle.Interp.Env V)[3]? = some (some (.op (.imm12 imm))) := rfl
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))]).run
      (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5155,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))]).run
      (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_5155,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx,sx⟩ := result
    obtain ⟨safeX,rx,mappedX,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    exact ⟨safeX,rx,mappedX⟩
/-- Actual immediate-emitter success derives the guarded request, mapped
register, exact producer and full marked state internally. -/
theorem stock_cmp_predecessor_unsigned_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (sz : OperandSize)
    {st next : State} {tr trace : Array RuleId} {n x : Nat} {literal : Int} {imm : Imm12} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+100) rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value x),some (.int literal),some (.op (.imm12 imm))]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
      out = .data 123 2 [.data 47 1 [.data 58 4 [.data 59 10 [],
        .data 93 (if sz = .size32 then 0 else 1) [],.reg .xzr,.reg rx,.op (.imm12 imm)]],
        .data 96 (condOf .ugt).idx []] ∧ next = st.mark x := by
  obtain ⟨safeX,rx,mappedX⟩ := stock_cmp_predecessor_unsigned_rhs_requests hp ctx hc sz run
  have replay := stock_cmp_predecessor_unsigned_rhs hp ctx hc sz st tr n x literal rx imm mappedX safeX
  rw [run] at replay
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
  exact ⟨safeX,rx,mappedX,replay.1,replay.2.1⟩
private def fixtureCtx : Ctx := {sinkCtx with
  valDef := #[none,none]
  valReg := #[some (.vreg 1 .int),some (.vreg 3 .int)]}
/-- Both machine widths and its fixed condition inhabit the real guarded
emitter RHS, including distinct mapped operands and the real source demand mark. -/
theorem stock_cmp_predecessor_unsigned_rhs_witness (sz : OperandSize) (literal : Int) (imm : Imm12) :
    ∃ out trace,(evalExpr program (Stock.sem fixtureCtx) {} 1000 rule_inst_5155.rhs
      #[some (.ty (.int sz.bits)),some (.value 0),some (.int literal),some (.op (.imm12 imm))]).run
      (sinkState,#[]) = .ok (some out,sinkState.mark 0,trace) ∧
      CondShape out (fun _ => True) := by
  have safe0 : DemandAllowed fixtureCtx sinkState 0 := by
    intro i impossible
    change none = some i at impossible
    cases impossible
  have actual := stock_cmp_predecessor_unsigned_rhs data_program fixtureCtx (cfg := {}) rfl sz sinkState #[] 900 0 literal
    (.vreg 1 .int) imm rfl safe0
  refine ⟨_,_,actual,Or.inr (Or.inr ⟨_,
    MInst.aluRRImm12 .subS sz .xzr (.vreg 1 .int) imm,condOf .ugt,rfl,?_,
    (condOf_ne_al .ugt).1,(condOf_ne_al .ugt).2,rfl,fun _ _ => trivial⟩)⟩
  cases sz <;> rfl
end Backend.Stock.Proof.ScalarCmp

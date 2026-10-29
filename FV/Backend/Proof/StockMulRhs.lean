module

public import FV.Backend.Proof.StockMulHelper
public import FV.Backend.Proof.StockRequestSuccess

@[expose] public section

namespace Backend.Stock.Proof.ScalarMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,stock_sem_ctor]
/-- The actual Stock multiplication root marks both operands and emits the saved ALU helper
code using their mapped registers, without assuming source IDs are vreg numbers. -/
theorem stock_mul_rhs_run {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w : Nat} {rx ry : Reg}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.base.fresh .int).1 rx ry .xzr)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have yPut := stock_put_in_reg ctx (st.mark x) y ry hy safeY
  have mulRun := fun q trace fuel => stock_madd_helper hp ctx hc (w := w) hw q trace fuel rx ry .xzr
  have outputRun := fun q trace fuel r => output_run hp ctx hc q trace fuel r
  have zero : ∀ q, Stock.externCtor ctx T.zero_reg [] q = .ok (.reg .xzr,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.zero_reg _ q (by decide)]
    rfl
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, zero, rule_lower_871, stock_sem_ctor]
    rfl

/-- Successful execution of the selected multiplication RHS supplies both scalar request
facts: safe definitions and mapped registers. These are not input certificates. -/
theorem stock_mul_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false)
    {x y w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_871, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_871, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx, sx⟩ := result
    obtain ⟨safeX, rx, mappedX, rfl, rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_871, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | unmodeled e =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_871.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_871, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨vy, sy⟩ := result
      obtain ⟨safeY, ry, mappedY, _, _⟩ := (stock_put_in_reg_iff ctx (st.mark x) y vy sy).mp yCall
      exact ⟨safeX, safeY, rx, ry, mappedX, mappedY⟩


/-- A successful actual multiply RHS supplies its guarded requests and complete
fresh output/state; source safety is derived from execution. -/
theorem stock_mul_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w n : Nat} (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+40) rule_lower_871.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧ ∃ rx ry,
      ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.base.fresh .int).1 rx ry .xzr)} := by
  obtain ⟨safeX,safeY,rx,ry,mx,my⟩ := stock_mul_rhs_requests hp ctx hc run
  obtain ⟨trace',expected⟩ := stock_mul_rhs_run hp ctx hc mx my width st safeX safeY tr n
  have same := Except.ok.inj (run.symm.trans expected)
  have outputEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safeX,safeY,rx,ry,mx,my,outputEq,stateEq⟩
end Backend.Stock.Proof.ScalarMul

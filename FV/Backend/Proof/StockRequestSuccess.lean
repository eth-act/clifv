import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselCtlTry

/-! Successful scalar requests supply their own guard and mapped-register facts. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem scalar_shape (ctx : Ctx) (st : State) (x : Nat) :
    Stock.externCtor ctx T.put_in_reg [.value x] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}" else
          match ctx.valueReg? x with
          | some r => .ok (.reg r, st.mark x)
          | none => .unmodeled s!"put_in_reg v{x}"
      | none => match ctx.valueReg? x with
        | some r => .ok (.reg r, st.mark x)
        | none => .unmodeled s!"put_in_reg v{x}" := by
  have legacy : Backend.externCtor ctx T.put_in_reg [.value x] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.reg r, (st.mark x).base)
      | none => .unmodeled s!"put_in_reg v{x}" := rfl
  have delegated : (match Backend.externCtor ctx T.put_in_reg [.value x] (st.mark x).base with
      | .ok (v, b) => ExtResult.ok (v, {st.mark x with base := b})
      | .fail => ExtResult.fail | .unmodeled e => ExtResult.unmodeled e) =
      (match ctx.valueReg? x with
      | some r => .ok (.reg r, st.mark x)
      | none => .unmodeled s!"put_in_reg v{x}") := by
    rw [legacy]
    cases ctx.valueReg? x <;> rfl
  simp only [T.put_in_reg] at delegated
  cases hd : ctx.defInst? x <;>
    simp [Stock.externCtor, T.put_in_reg, TId.mark_value_used, hd] <;>
      first | exact delegated | (split <;> first | rfl | exact delegated)

/-- Successful actual scalar requests certify source safety, the register map,
output and complete marked state; no independently supplied safety premise. -/
theorem stock_put_in_reg_iff (ctx : Ctx) (st : State) (x : Nat) (v : V) (next : State) :
    Stock.externCtor ctx T.put_in_reg [.value x] st = .ok (v, next) ↔
      DemandAllowed ctx st x ∧ ∃ r, ctx.valueReg? x = some r ∧ v = .reg r ∧ next = st.mark x := by
  constructor
  · intro run
    rw [scalar_shape] at run
    cases hd : ctx.defInst? x with
    | none =>
      rw [hd] at run
      cases hm : ctx.valueReg? x with
      | none => rw [hm] at run; cases run
      | some r =>
        rw [hm] at run
        cases run
        refine ⟨?_, r, rfl, rfl, rfl⟩
        intro i impossible
        rw [hd] at impossible
        cases impossible
    | some i =>
      rw [hd] at run
      cases hs : st.sunk[i]! with
      | true => simp only [hs, ite_true] at run; cases run
      | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at run
        cases hm : ctx.valueReg? x with
        | none => rw [hm] at run; cases run
        | some r =>
          rw [hm] at run
          cases run
          refine ⟨?_, r, rfl, rfl, rfl⟩
          intro j defined
          rw [hd] at defined
          have same := Option.some.inj defined
          subst j
          exact hs
  · rintro ⟨safe, r, mapped, rfl, rfl⟩
    exact stock_put_in_reg ctx st x r mapped safe

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

/-- Successful execution of the selected add RHS supplies both scalar request
facts: safe definitions and mapped registers. These are not input certificates. -/
theorem stock_rhs_86_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false)
    {x y w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_86, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_86, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx, sx⟩ := result
    obtain ⟨safeX, rx, mappedX, rfl, rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_86, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | unmodeled e =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_86, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨vy, sy⟩ := result
      obtain ⟨safeY, ry, mappedY, _, _⟩ := (stock_put_in_reg_iff ctx (st.mark x) y vy sy).mp yCall
      exact ⟨safeX, safeY, rx, ry, mappedX, mappedY⟩

/-- Successful execution of the selected subtraction RHS supplies both scalar request
facts: safe definitions and mapped registers. These are not input certificates. -/
theorem stock_rhs_801_requests {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false)
    {x y w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry := by
  cases xCall : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_801, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
        (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
      cases hp
      isel_eval [*, hc, rule_lower_801, stock_sem_ctor, xCall]
      intro impossible
      cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨vx, sx⟩ := result
    obtain ⟨safeX, rx, mappedX, rfl, rfl⟩ := (stock_put_in_reg_iff ctx st x vx sx).mp xCall
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_801, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | unmodeled e =>
      have denied : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
          (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) ≠ .ok (some out, next, trace) := by
        cases hp
        isel_eval [*, hc, rule_lower_801, stock_sem_ctor, xCall, yCall]
        intro impossible
        cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨vy, sy⟩ := result
      obtain ⟨safeY, ry, mappedY, _, _⟩ := (stock_put_in_reg_iff ctx (st.mark x) y vy sy).mp yCall
      exact ⟨safeX, safeY, rx, ry, mappedX, mappedY⟩

/-- A successful add RHS fixes its output and complete state from the actual
operand requests; safety and register mappings are derived internally. -/
theorem stock_rhs_86_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w n : Nat} (hw : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR .add (szOf w) (st.base.fresh .int).1 rx ry)} := by
  obtain ⟨safeX, safeY, rx, ry, mappedX, mappedY⟩ := stock_rhs_86_requests hp ctx hc run
  obtain ⟨expectedTrace, expected⟩ := stock_rhs_86 hp ctx hc mappedX mappedY hw st safeX safeY tr n
  rw [run] at expected
  have equal := Except.ok.inj expected
  have valueEq := congrArg (fun q => q.1) equal
  have stateEq := congrArg (fun q => q.2.1) equal
  exact ⟨rx, ry, mappedX, mappedY, Option.some.inj valueEq, stateEq⟩

/-- A successful sub RHS fixes its output and complete state from the actual
operand requests; safety and register mappings are derived internally. -/
theorem stock_rhs_801_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w n : Nat} (hw : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) = .ok (some out, next, trace)) :
    ∃ rx ry, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧
      out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 rx ry)} := by
  obtain ⟨safeX, safeY, rx, ry, mappedX, mappedY⟩ := stock_rhs_801_requests hp ctx hc run
  obtain ⟨expectedTrace, expected⟩ := stock_rhs_801 hp ctx hc mappedX mappedY hw st safeX safeY tr n
  rw [run] at expected
  have equal := Except.ok.inj expected
  have valueEq := congrArg (fun q => q.1) equal
  have stateEq := congrArg (fun q => q.2.1) equal
  exact ⟨rx, ry, mappedX, mappedY, Option.some.inj valueEq, stateEq⟩

/-- Both actual sparse-ID add/subtract roots at 32 and 64 bits inhabit the
request inversion and complete observed-state contracts. -/
theorem stock_request_success_witness (subtract : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (ctx : Ctx) (st next : State) (trace : Array RuleId),
      (evalExpr program (Stock.sem ctx) {} 40
        (if subtract then rule_lower_801 else rule_lower_86).rhs
        (env3 (.ty (.int ty.width)) (.value 7) (.value 31))).run (st, #[]) =
          .ok (some (.regsVec [[.vreg 195 .int]]), next, trace) ∧
      Stock.externCtor ctx T.put_in_reg [.value 7] st = .ok (.reg (.vreg 192 .int), st.mark 7) ∧
      DemandAllowed ctx st 7 ∧ DemandAllowed ctx st 31 ∧
      ∃ rx ry, ctx.valueReg? 7 = some rx ∧ ctx.valueReg? 31 = some ry ∧
        (.regsVec [[.vreg 195 .int]] : V) = .regsVec [[(st.base.fresh .int).1]] ∧
        next = {(st.mark 7).mark 31 with base := (st.base.fresh .int).2.emit (.aluRRR
          (if subtract then .sub else .add) (szOf ty.width) (st.base.fresh .int).1 rx ry)} := by
  obtain ⟨ctx, info, next, trace, regs, _, _, _, _, mx, _, _, _, evaluated, _⟩ :=
    stock_alu_roots_witness subtract ty supported
  have width : ty.width ≤ 64 := by rcases supported with rfl | rfl <;> decide
  cases subtract with
  | false =>
    obtain ⟨sx, sy, _, _, _, _⟩ := stock_rhs_86_requests data_program ctx (cfg := {}) rfl evaluated
    have scalar := (stock_put_in_reg_iff ctx _ 7 (.reg (.vreg 192 .int)) _).mpr
      ⟨sx, .vreg 192 .int, mx, rfl, rfl⟩
    have observed := stock_rhs_86_observed data_program ctx (cfg := {}) rfl width evaluated
    exact ⟨ctx, _, next, trace, evaluated, scalar, sx, sy, observed⟩
  | true =>
    obtain ⟨sx, sy, _, _, _, _⟩ := stock_rhs_801_requests data_program ctx (cfg := {}) rfl evaluated
    have scalar := (stock_put_in_reg_iff ctx _ 7 (.reg (.vreg 192 .int)) _).mpr
      ⟨sx, .vreg 192 .int, mx, rfl, rfl⟩
    have observed := stock_rhs_801_observed data_program ctx (cfg := {}) rfl width evaluated
    exact ⟨ctx, _, next, trace, evaluated, scalar, sx, sy, observed⟩

end Backend.Stock.Proof

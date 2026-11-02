import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockAddSubRhs
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
theorem stock_addsub_imm_first_request {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} {imm : Imm12}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (immRule subtract left).rhs
      (immEnv left w x imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (immRule subtract left).rhs
        (immEnv left w x imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_90,sem_ctor]
        intro impossible; cases impossible
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_93,sem_ctor]
        intro impossible; cases impossible
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_805,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (immRule subtract left).rhs
        (immEnv left w x imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_90,sem_ctor]
        intro impossible; cases impossible
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_93,sem_ctor]
        intro impossible; cases impossible
      · simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_805,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
theorem stock_addsub_neg_imm_first_request {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} {y : Nat} {imm : Imm12}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+50) (negImmRule subtract left).rhs
      (negImmEnv left w x y imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (negImmRule subtract left).rhs
        (negImmEnv left w x y imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_98,sem_ctor]
        intro impossible; cases impossible
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_102,sem_ctor]
        intro impossible; cases impossible
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_810,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+50) (negImmRule subtract left).rhs
        (negImmEnv left w x y imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_98,sem_ctor]
        intro impossible; cases impossible
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_102,sem_ctor]
        intro impossible; cases impossible
      · simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_810,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
theorem stock_addsub_extend_first_request {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} {z : Nat} {e : ExtendOp}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
      (extendEnv left w x z e)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
        (extendEnv left w x z e)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_108,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_111,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_816,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
        (extendEnv left w x z e)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_108,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_111,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_816,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
theorem stock_addsub_shift_first_request {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x n : Nat} {z y : Nat} {c : Int} {sh : ShiftOpAndAmt}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
      (shiftEnv left w x z y c sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
        (shiftEnv left w x z y c sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_116,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_120,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_821,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
        (shiftEnv left w x z y c sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_116,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_120,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_821,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
theorem stock_addsub_shift_requests {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x z y n : Nat} {c : Int} {sh : ShiftOpAndAmt}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
      (shiftEnv left w x z y c sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st z ∧
      ∃ rx rz,ctx.valueReg? x = some rx ∧ ctx.valueReg? z = some rz := by
  obtain ⟨safeX,rx,mapX⟩ := stock_addsub_shift_first_request hp ctx subtract left side run
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  cases requestZ : Stock.externCtor ctx T.put_in_reg [.value z] (st.mark x) with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
        (shiftEnv left w x z y c sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_116,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_120,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_821,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
        (shiftEnv left w x z y c sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_116,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_120,sem_ctor]
        intro impossible; cases impossible
      · simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_821,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safeZ,rz,mapZ,_,_⟩ := (stock_put_in_reg_iff ctx (st.mark x) z v q).mp requestZ
    exact ⟨safeX,safeZ,rx,rz,mapX,mapZ⟩
private theorem extended_shape (ctx : Ctx) (st : State) (x : Nat) (e : ExtendOp) :
    Stock.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st =
      match ctx.defInst? x with
      | some i => if st.sunk[i]! then .unmodeled s!"demand for sunk instruction {i}" else
          match ctx.valueReg? x with
          | some r => .ok (.reg r, st.mark x)
          | none => .unmodeled "put_extended_in_reg"
      | none => match ctx.valueReg? x with
        | some r => .ok (.reg r, st.mark x)
        | none => .unmodeled "put_extended_in_reg" := by
  have legacy : Backend.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] (st.mark x).base =
      match ctx.valueReg? x with
      | some r => .ok (.reg r, (st.mark x).base)
      | none => .unmodeled "put_extended_in_reg" := rfl
  have delegated : (match Backend.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] (st.mark x).base with
      | .ok (v, b) => ExtResult.ok (v, {st.mark x with base := b})
      | .fail => ExtResult.fail | .unmodeled e => ExtResult.unmodeled e) =
      (match ctx.valueReg? x with
      | some r => .ok (.reg r, st.mark x)
      | none => .unmodeled "put_extended_in_reg") := by
    rw [legacy]
    cases ctx.valueReg? x <;> rfl
  simp only [T.put_extended_in_reg] at delegated
  cases hd : ctx.defInst? x <;>
    simp [Stock.externCtor, T.put_extended_in_reg, TId.mark_value_used, hd] <;>
      first | exact delegated | (split <;> first | rfl | exact delegated)

/-- Successful actual scalar requests certify source safety, the register map,
output and complete marked state; no independently supplied safety premise. -/
theorem stock_addsub_put_extended_iff (ctx : Ctx) (st : State) (x : Nat) (e : ExtendOp) (v : V) (next : State) :
    Stock.externCtor ctx T.put_extended_in_reg [.op (.extended x e)] st = .ok (v, next) ↔
      DemandAllowed ctx st x ∧ ∃ r, ctx.valueReg? x = some r ∧ v = .reg r ∧ next = st.mark x := by
  constructor
  · intro run
    rw [extended_shape ctx st x e] at run
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
    exact stock_put_extended_in_reg ctx st x e r mapped safe

theorem stock_addsub_extend_requests {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x z n : Nat} {e : ExtendOp}
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
      (extendEnv left w x z e)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st z ∧
      ∃ rx rz,ctx.valueReg? x = some rx ∧ ctx.valueReg? z = some rz := by
  obtain ⟨safeX,rx,mapX⟩ := stock_addsub_extend_first_request hp ctx subtract left side run
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  cases requestZ : Stock.externCtor ctx T.put_extended_in_reg [.op (.extended z e)] (st.mark x) with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
        (extendEnv left w x z e)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_108,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_111,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_816,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
        (extendEnv left w x z e)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases subtract <;> cases left
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_108,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_111,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false]
        isel_eval [*,rule_lower_816,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor]
        intro impossible; cases impossible
      · cases side rfl
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safeZ,rz,mapZ,_,_⟩ := (stock_addsub_put_extended_iff ctx (st.mark x) z e v q).mp requestZ
    exact ⟨safeX,safeZ,rx,rz,mapX,mapZ⟩
end Backend.Stock.Proof.ScalarAddSub

import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.StockRequestSuccess

namespace Backend.Stock.Proof.Bnot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def rule (shifted : Bool) : Rule := if shifted then rule_lower_1401 else rule_lower_1377
def env (shifted : Bool) (w x : Nat) (k : Int) (sh : ShiftOpAndAmt) : Isle.Interp.Env V :=
  if shifted then env4 (.ty (.int w)) (.value x) (.int k) (.op (.shiftOpAndAmt sh))
  else env2 (.ty (.int w)) (.value x)
def code (shifted : Bool) (w : Nat) (d r : Reg) (sh : ShiftOpAndAmt) : MInst :=
  if shifted then .aluRRRShift .orrNot (szOf w) d .xzr r sh else .aluRRR .orrNot (szOf w) d .xzr r

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem zero_reg (ctx : Ctx) (st : State) :
    (Stock.sem ctx).ctor T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [sem_ctor,stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]
  rfl
private theorem value_reg (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.value_reg [.reg r] st = .ok (.regs [r],st) := by
  rw [sem_ctor,stock_ctor_baseOnly ctx T.value_reg _ st (by decide)]
  rfl
private theorem output (ctx : Ctx) (st : State) (r : Reg) :
    (Stock.sem ctx).ctor T.output [.regs [r]] st = .ok (.regsVec [[r]],st) := by
  rw [sem_ctor,stock_ctor_baseOnly ctx T.output _ st (by decide)]
  rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have a := value_reg ctx st r
  have b := output ctx st r
  rw [sem_ctor] at a b
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]
private theorem orr_not {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 495 [.ty (.int w),.reg .xzr,.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),{st with base := (st.base.fresh .int).2.emit (code false w (st.base.fresh .int).1 r ⟨.lsl,0⟩)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3403.id) := by
  have inner := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl width (k := 3) (op := .orrNot) rfl q trace fuel .xzr r
  cases hp
  isel_eval [*,rule_inst_3403,code,sem_mkData]
private theorem orr_not_shift {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) (sh : ShiftOpAndAmt) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 496 [.ty (.int w),.reg .xzr,.reg r,.op (.shiftOpAndAmt sh)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),{st with base := (st.base.fresh .int).2.emit (code true w (st.base.fresh .int).1 r sh)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2656.id).push rule_inst_3407.id) := by
  have inner := fun q trace fuel => LogicalForms.stock_logical_shift_helper hp ctx (cfg := {}) rfl width
    (k := 3) (op := .orrNot) rfl q trace fuel .xzr r sh
  cases hp
  isel_eval [*,rule_inst_3407,code,sem_mkData]

/-- Actual base and fused-shift NOT RHS executions account for mapped requests,
marking, fresh output and the complete scheduling state. -/
theorem stock_bnot_rhs_run {p : Program} (hp : Data p) (ctx : Ctx) (shifted : Bool)
    {w x : Nat} {k : Int} {sh : ShiftOpAndAmt} (width : w ≤ 64)
    {r : Reg} (mapped : ctx.valueReg? x = some r) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) {} (n+40) (rule shifted).rhs (env shifted w x k sh)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (code shifted w (st.base.fresh .int).1 r sh)},trace) := by
  have request := stock_put_in_reg ctx st x r mapped safe
  have zero := fun q => zero_reg ctx q
  have wrapped := fun q trace fuel rr => output_run hp ctx q trace fuel rr
  have base := fun q trace fuel => orr_not hp ctx width q trace fuel r
  have shift := fun q trace fuel => orr_not_shift hp ctx width q trace fuel r sh
  simp only [sem_ctor] at zero
  cases shifted
  · cases hp
    refine Exists.intro ?trace0 ?proof0
    case proof0 =>
      isel_eval [*,rule,env,code,rule_lower_1377,sem_ctor]
      rfl
  · cases hp
    refine Exists.intro ?trace1 ?proof1
    case proof1 =>
      isel_eval [*,rule,env,code,rule_lower_1401,sem_ctor]
      rfl

private theorem requested {p : Program} (hp : Data p) (ctx : Ctx) (shifted : Bool)
    {w x n : Nat} {k : Int} {sh : ShiftOpAndAmt} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (rule shifted).rhs (env shifted w x k sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ r, ctx.valueReg? x = some r := by
  have zero := fun q => zero_reg ctx q
  simp only [sem_ctor] at zero
  cases called : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (rule shifted).rhs (env shifted w x k sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases shifted <;> cases hp <;> isel_eval [*,rule,env,rule_lower_1377,rule_lower_1401,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (rule shifted).rhs (env shifted w x k sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases shifted <;> cases hp <;> isel_eval [*,rule,env,rule_lower_1377,rule_lower_1401,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,r,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x value after).mp called
    exact ⟨safe,r,mapped⟩

/-- Successful selected RHS supplies its own request and exact output/state;
no register request certificate is supplied by the caller. -/
theorem stock_bnot_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (shifted : Bool)
    {w x n : Nat} {k : Int} {sh : ShiftOpAndAmt} (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (rule shifted).rhs (env shifted w x k sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ r, ctx.valueReg? x = some r ∧ out = .regsVec [[(st.base.fresh .int).1]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (code shifted w (st.base.fresh .int).1 r sh)} := by
  obtain ⟨safe,r,mapped⟩ := requested hp ctx shifted run
  obtain ⟨trace',expected⟩ := stock_bnot_rhs_run hp ctx shifted width mapped st safe tr n
  have same := Except.ok.inj (run.symm.trans expected)
  have outputEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safe,r,mapped,outputEq,stateEq⟩

end Backend.Stock.Proof.Bnot

import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockLogicalRrr
import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.StockLogicalLookthrough

namespace Backend.Stock.Proof.LogicalSemantics
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

private theorem imm_requests {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y n : Nat} {kk : Int} {imm : ImmLogic} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs
      (logicalImmEnv left k w x y kk imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st (if left then y else x) ∧ ∃ rx, ctx.valueReg? (if left then y else x) = some rx := by
  cases called : Stock.externCtor ctx T.put_in_reg [.value (if left then y else x)] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs
        (logicalImmEnv left k w x y kk imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called <;>
        isel_eval [*,logicalImmEnv,rule_inst_3920,rule_inst_3923,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs
        (logicalImmEnv left k w x y kk imm)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called <;>
        isel_eval [*,logicalImmEnv,rule_inst_3920,rule_inst_3923,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st _ value after).mp called
    exact ⟨safe,rx,mapped⟩

/-- Successful actual immediate RHS derives its safe mapped request and complete
fresh allocation/emission state; no request or code certificates are inputs. -/
theorem stock_logical_imm_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y n : Nat} {kk : Int} {imm : ImmLogic} {op : ALUOp}
    (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs
      (logicalImmEnv left k w x y kk imm)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st (if left then y else x) ∧ ∃ rx,
      ctx.valueReg? (if left then y else x) = some rx ∧ out = .reg (st.base.fresh .int).1 ∧
      next = {st.mark (if left then y else x) with
        base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)} := by
  obtain ⟨safe,rx,mapped⟩ := imm_requests hp ctx left run
  have expected : ∃ trace', (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3923 else rule_inst_3920).rhs
      (logicalImmEnv left k w x y kk imm)).run (st,tr) = .ok (some (.reg (st.base.fresh .int).1),
        {st.mark (if left then y else x) with
          base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)},trace') := by
    cases left
    · exact LogicalForms.stock_rhs_3920 hp ctx rfl tag mapped width st safe tr n
    · exact LogicalForms.stock_rhs_3923 hp ctx rfl tag mapped width st safe tr n
  obtain ⟨trace',expected⟩ := expected
  have same := Except.ok.inj (run.symm.trans expected)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safe,rx,mapped,outEq,stateEq⟩

private theorem shift_requests {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y z n : Nat} {kk : Int} {sh : ShiftOpAndAmt} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
      (logicalShiftEnv left k w x y z kk sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st (if left then y else x) ∧ DemandAllowed ctx st z ∧
      ∃ rx rz, ctx.valueReg? (if left then y else x) = some rx ∧ ctx.valueReg? z = some rz := by
  cases called : Stock.externCtor ctx T.put_in_reg [.value (if left then y else x)] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
        (logicalShiftEnv left k w x y z kk sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called <;>
        isel_eval [*,logicalShiftEnv,rule_inst_3928,rule_inst_3931,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
        (logicalShiftEnv left k w x y z kk sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called <;>
        isel_eval [*,logicalShiftEnv,rule_inst_3928,rule_inst_3931,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st _ value after).mp called
    cases zCall : Stock.externCtor ctx T.put_in_reg [.value z] (st.mark (if left then y else x)) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
          (logicalShiftEnv left k w x y z kk sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called zCall <;>
          isel_eval [*,logicalShiftEnv,rule_inst_3928,rule_inst_3931,stock_sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | unmodeled err =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
          (logicalShiftEnv left k w x y z kk sh)).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        cases left <;> simp only [Bool.false_eq_true,ite_false,ite_true] at called zCall <;>
          isel_eval [*,logicalShiftEnv,rule_inst_3928,rule_inst_3931,stock_sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨value,after⟩ := result
      obtain ⟨safeZ,rz,mappedZ,_,_⟩ := (stock_put_in_reg_iff ctx (st.mark (if left then y else x)) z value after).mp zCall
      exact ⟨safe,safeZ,rx,rz,mapped,mappedZ⟩

/-- Successful actual shift RHS derives both safe mapped requests and its full
fresh allocation/emission state, rather than accepting request/code receipts. -/
theorem stock_logical_shift_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {k w x y z n : Nat} {kk : Int} {sh : ShiftOpAndAmt} {op : ALUOp}
    (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
      (logicalShiftEnv left k w x y z kk sh)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st (if left then y else x) ∧ DemandAllowed ctx st z ∧ ∃ rx rz,
      ctx.valueReg? (if left then y else x) = some rx ∧ ctx.valueReg? z = some rz ∧
      out = .reg (st.base.fresh .int).1 ∧ next = {(st.mark (if left then y else x)).mark z with
        base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx rz sh)} := by
  obtain ⟨safe,safeZ,rx,rz,mapped,mappedZ⟩ := shift_requests hp ctx left run
  have expected : ∃ trace', (evalExpr p (Stock.sem ctx) {} (n + 40) (if left then rule_inst_3931 else rule_inst_3928).rhs
      (logicalShiftEnv left k w x y z kk sh)).run (st,tr) = .ok (some (.reg (st.base.fresh .int).1),
        {(st.mark (if left then y else x)).mark z with
          base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx rz sh)},trace') := by
    cases left
    · exact LogicalForms.stock_rhs_3928 hp ctx rfl tag mapped mappedZ width st safe safeZ tr n
    · exact LogicalForms.stock_rhs_3931 hp ctx rfl tag mapped mappedZ width st safe safeZ tr n
  obtain ⟨trace',expected⟩ := expected
  have same := Except.ok.inj (run.symm.trans expected)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safe,safeZ,rx,rz,mapped,mappedZ,outEq,stateEq⟩

/-- Both actual immediate RHS forms inhabit the request/state observations at
32/64 bits, with their mapped source and fresh destination. -/
theorem stock_logical_imm_observed_witness (left : Bool) (w : Nat) (supported : w = 32 ∨ w = 64) :
    ∃ (next : State) (trace : Array RuleId) (rx : Reg),
      (evalExpr program (Stock.sem sinkCtx) {} 40 (if left then rule_inst_3923 else rule_inst_3920).rhs
        (logicalImmEnv left 2 w 0 1 255 ⟨255,szOf w⟩)).run (sinkState,#[]) =
          .ok (some (.reg (.vreg 194 .int)),next,trace) ∧
      DemandAllowed sinkCtx sinkState (if left then 1 else 0) ∧
      sinkCtx.valueReg? (if left then 1 else 0) = some rx ∧
      next = {sinkState.mark (if left then 1 else 0) with base := (sinkState.base.fresh .int).2.emit (.aluRRImmLogic .orr (szOf w) (.vreg 194 .int) rx ⟨255,szOf w⟩)} := by
  obtain ⟨a,b,c,d,ta,tb,tc,td,_,_,ra,rb,rc,rd,_⟩ := LogicalForms.stock_logical_forms_witness w supported
  have width : w ≤ 64 := by rcases supported with rfl | rfl <;> decide
  cases left
  · obtain ⟨safe,rx,mapped,out,state⟩ := stock_logical_imm_rhs_observed data_program sinkCtx false rfl width (x := 0) (y := 1) (n := 0) ra
    exact ⟨a,ta,rx,ra,safe,mapped,state⟩
  · obtain ⟨safe,rx,mapped,out,state⟩ := stock_logical_imm_rhs_observed data_program sinkCtx true rfl width (x := 0) (y := 1) (n := 0) rb
    exact ⟨b,tb,rx,rb,safe,mapped,state⟩

/-- Both actual shifted RHS forms inhabit complete two-request observations at
32/64 bits; the untouched Stock fields and fresh emission are derived. -/
theorem stock_logical_shift_observed_witness (left : Bool) (w : Nat) (supported : w = 32 ∨ w = 64) :
    ∃ (next : State) (trace : Array RuleId) (rx rz : Reg),
      (evalExpr program (Stock.sem sinkCtx) {} 40 (if left then rule_inst_3931 else rule_inst_3928).rhs
        (logicalShiftEnv left 2 w 0 0 1 3 ⟨.lsl,3⟩)).run (sinkState,#[]) =
          .ok (some (.reg (.vreg 194 .int)),next,trace) ∧
      DemandAllowed sinkCtx sinkState 0 ∧ DemandAllowed sinkCtx sinkState 1 ∧
      sinkCtx.valueReg? 0 = some rx ∧ sinkCtx.valueReg? 1 = some rz ∧
      next = {(sinkState.mark 0).mark 1 with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .orr (szOf w) (.vreg 194 .int) rx rz ⟨.lsl,3⟩)} := by
  obtain ⟨a,b,c,d,ta,tb,tc,td,_,_,ra,rb,rc,rd,_⟩ := LogicalForms.stock_logical_forms_witness w supported
  have width : w ≤ 64 := by rcases supported with rfl | rfl <;> decide
  cases left
  · obtain ⟨safe,safeZ,rx,rz,mapped,mappedZ,out,state⟩ := stock_logical_shift_rhs_observed
      data_program sinkCtx false rfl width (x := 0) (y := 0) (n := 0) rc
    exact ⟨c,tc,rx,rz,rc,safe,safeZ,mapped,mappedZ,state⟩
  · obtain ⟨safe,safeZ,rx,rz,mapped,mappedZ,out,state⟩ := stock_logical_shift_rhs_observed
      data_program sinkCtx true rfl width (x := 0) (y := 0) (n := 0) rd
    exact ⟨d,td,rx,rz,rd,safe,safeZ,mapped,mappedZ,state⟩

private theorem rrr_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {k w x y n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
      (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧
      ∃ rx rz, ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some rz := by
  cases called : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_3916,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_3916,stock_sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st _ value after).mp called
    cases yCall : Stock.externCtor ctx T.put_in_reg [.value y] (st.mark x) with
    | fail =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
          (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_3916,stock_sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | unmodeled err =>
      have denied : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
          (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) ≠ .ok (some out,next,trace) := by
        cases hp
        isel_eval [*,rule_inst_3916,stock_sem_ctor]
        all_goals intro impossible; cases impossible
      exact False.elim (denied run)
    | ok result =>
      obtain ⟨value,after⟩ := result
      obtain ⟨safeZ,rz,mappedZ,_,_⟩ := (stock_put_in_reg_iff ctx (st.mark x) y value after).mp yCall
      exact ⟨safe,safeZ,rx,rz,mapped,mappedZ⟩

/-- Successful actual register-only logical RHS supplies both mapped requests
and the complete marked/fresh/emitted state, including its observed output. -/
theorem stock_logical_rrr_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {k w x y n : Nat} {op : ALUOp} (tag : ALUOp.ofIdx? k = some op) (width : w ≤ 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n + 40) rule_inst_3916.rhs
      (env4 (.data 59 k []) (.ty (.int w)) (.value x) (.value y))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ DemandAllowed ctx st y ∧ ∃ rx ry,
      ctx.valueReg? x = some rx ∧ ctx.valueReg? y = some ry ∧ out = .reg (st.base.fresh .int).1 ∧
      next = {(st.mark x).mark y with
        base := (st.base.fresh .int).2.emit (.aluRRR op (szOf w) (st.base.fresh .int).1 rx ry)} := by
  obtain ⟨safeX,safeY,rx,ry,mappedX,mappedY⟩ := rrr_requests hp ctx run
  obtain ⟨trace',expected⟩ := stock_rhs_3916 hp ctx (cfg := {}) rfl tag mappedX mappedY width st safeX safeY tr n
  have same := Except.ok.inj (run.symm.trans expected)
  have outEq := Option.some.inj (congrArg Prod.fst same)
  have stateEq := congrArg (fun q => q.2.1) same
  exact ⟨safeX,safeY,rx,ry,mappedX,mappedY,outEq,stateEq⟩

/-- Real sparse-ID logical register RHS executions at32/64 bits inhabit the
complete request/state observation for all commutative logical operations. -/
theorem stock_logical_rrr_observed_witness (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64)
    (k : Nat) (op : ALUOp) (cop : Clif.BinaryOp) (tag : ALUOp.ofIdx? k = some op) (operation : LogicPair op cop) :
    ∃ (ctx : Ctx) (st next : State) (trace : Array RuleId) (rx ry : Reg),
      (evalExpr program (Stock.sem ctx) {} 40 rule_inst_3916.rhs
        (env4 (.data 59 k []) (.ty (.int ty.width)) (.value 7) (.value 31))).run (st,#[]) =
          .ok (some (.reg (st.base.fresh .int).1),next,trace) ∧
      DemandAllowed ctx st 7 ∧ DemandAllowed ctx st 31 ∧
      ctx.valueReg? 7 = some rx ∧ ctx.valueReg? 31 = some ry ∧
      next = {(st.mark 7).mark 31 with
        base := (st.base.fresh .int).2.emit (.aluRRR op (szOf ty.width) (st.base.fresh .int).1 rx ry)} := by
  obtain ⟨ctx,next,trace,regs,_,_,_,rhs,_⟩ := stock_logical_rrr_witness ty supported k op cop tag operation
  have width : ty.width ≤ 64 := by rcases supported with rfl | rfl <;> decide
  obtain ⟨safeX,safeY,rx,ry,mappedX,mappedY,out,state⟩ := stock_logical_rrr_rhs_observed
    data_program ctx tag width (n := 0) rhs
  exact ⟨ctx,_,next,trace,rx,ry,rhs,safeX,safeY,mappedX,mappedY,state⟩

end Backend.Stock.Proof.LogicalSemantics

import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.IselRulesALU
import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.IselTermsLogic
import FV.Backend.Proof.IselCtlTry

/-! Stock logical immediate and shifted-register helpers reuse pure ALU semantics.
Actual RHS cases retain mapped registers while recording selected-code demand. -/
namespace Backend.Stock.Proof.LogicalForms
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def aluScope : List Nat := [164, 170, 172, 175, 201, 235, 305, 362, 432, 437, 1820, 1962, 1963, 2028, 2029, 360, 377, 1823, 1825]
private theorem alu_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx)
      (fun t => t ∈ aluScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [aluScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t170] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t172] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t175] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t201] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t235] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t305] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t362] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t432] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t437] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1820] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1962] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1963] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2028] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2029] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t360] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t377] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1823] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1825] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
  · intro t term member lookup flags ex kind r recorded
    simp only [aluScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t164] at lookup
      cases lookup
      cases kind
    · rw [hp.t170] at lookup
      cases lookup
      cases kind
    · rw [hp.t172] at lookup
      cases lookup
      rw [hp.r172] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_prelude_lower_105]
    · rw [hp.t175] at lookup
      cases lookup
      cases kind
    · rw [hp.t201] at lookup
      cases lookup
      cases kind
    · rw [hp.t235] at lookup
      cases lookup
      cases kind
    · rw [hp.t305] at lookup
      cases lookup
      rw [hp.r305] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl | rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_1592, rule_inst_1593]
    · rw [hp.t362] at lookup
      cases lookup
      rw [hp.r362] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_2545]
    · rw [hp.t432] at lookup
      cases lookup
      rw [hp.r432] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_3118]
    · rw [hp.t437] at lookup
      cases lookup
      rw [hp.r437] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_3138]
    · rw [hp.t1820] at lookup
      cases lookup
      cases kind
    · rw [hp.t1962] at lookup
      cases lookup
      cases kind
    · rw [hp.t1963] at lookup
      cases lookup
      cases kind
    · rw [hp.t2028] at lookup
      cases lookup
      cases kind
    · rw [hp.t2029] at lookup
      cases lookup
      cases kind
    · rw [hp.t360] at lookup
      cases lookup
      rw [hp.r360] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_2529]
    · rw [hp.t377] at lookup
      cases lookup
      rw [hp.r377] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, aluScope, rule_inst_2656]
    · rw [hp.t1823] at lookup
      cases lookup
      cases kind
    · rw [hp.t1825] at lookup
      cases lookup
      cases kind

private def frameCtor (ctx : Ctx) (t : Term) (vs : List V) (st : State) : ExtResult (V × State) :=
  match Backend.externCtor ctx t vs st.base with
  | .ok (v, base) => .ok (v, {st with base})
  | .fail => .fail
  | .unmodeled e => .unmodeled e
private def frameSem (ctx : Ctx) : Isle.Sem V State :=
  (Backend.sem ctx).restate (frameCtor ctx)
    (fun t v st => Backend.externExtract ctx t v st.base)
private def scheduling (st : State) : State := {st with base := default}
private theorem frame_presAt (p : Program) (ctx : Ctx) (cfg : Config) (n : Nat) :
    PresAt p (frameSem ctx) cfg (fun st next => scheduling next = scheduling st) n := by
  apply presAt (R := fun st next => scheduling next = scheduling st)
    (fun _ => rfl) (fun _ _ _ ab bc => bc.trans ab)
  intro t vs st v next run
  change frameCtor ctx t vs st = .ok (v, next) at run
  unfold frameCtor at run
  split at run <;> cases run
  rfl
private theorem frame_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx) (fun t => t ∈ aluScope) := by
  constructor
  · intro t term member lookup vs st
    have unchanged : term.id ∉ revisedCtors := by
      simp only [aluScope, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.t164] at lookup
        cases lookup
        decide
      · rw [hp.t170] at lookup
        cases lookup
        decide
      · rw [hp.t172] at lookup
        cases lookup
        decide
      · rw [hp.t175] at lookup
        cases lookup
        decide
      · rw [hp.t201] at lookup
        cases lookup
        decide
      · rw [hp.t235] at lookup
        cases lookup
        decide
      · rw [hp.t305] at lookup
        cases lookup
        decide
      · rw [hp.t362] at lookup
        cases lookup
        decide
      · rw [hp.t432] at lookup
        cases lookup
        decide
      · rw [hp.t437] at lookup
        cases lookup
        decide
      · rw [hp.t1820] at lookup
        cases lookup
        decide
      · rw [hp.t1962] at lookup
        cases lookup
        decide
      · rw [hp.t1963] at lookup
        cases lookup
        decide
      · rw [hp.t2028] at lookup
        cases lookup
        decide
      · rw [hp.t2029] at lookup
        cases lookup
        decide
      · rw [hp.t360] at lookup
        cases lookup
        decide
      · rw [hp.t377] at lookup
        cases lookup
        decide
      · rw [hp.t1823] at lookup
        cases lookup
        decide
      · rw [hp.t1825] at lookup
        cases lookup
        decide
    change projectCtor id (Stock.externCtor ctx term vs st) = frameCtor ctx term vs st
    rw [stock_ctor_baseOnly _ _ _ _ unchanged]
    unfold frameCtor
    cases Backend.externCtor ctx term vs st.base with
    | ok pair => cases pair; rfl
    | fail => rfl
    | unmodeled e => rfl
  · exact (alu_scope hp ctx).rules

private theorem pure_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel ty t : Nat} {vs : List V} (allowed : t ∈ aluScope)
    {st : State} {base : LState} {tr trace : Array RuleId} {v : Option V}
    (legacy : (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base, tr) = .ok (v, base, trace)) :
    (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr) =
      .ok (v, {st with base}, trace) := by
  have projection := (evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ aluScope) (alu_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
  change projectResult State.base ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr)) =
    (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base, tr) at projection
  rw [legacy] at projection
  cases actual : (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr) with
  | error err => rw [actual] at projection; cases projection
  | ok output =>
    obtain ⟨out, next, rules⟩ := output
    rw [actual] at projection
    simp only [projectResult, Except.ok.injEq, Prod.mk.injEq] at projection
    obtain ⟨rfl, baseEq, rfl⟩ := projection
    have framed := (evaluation_scoped_restate p (frameSem ctx) cfg hc id
      (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
      (fun t => t ∈ aluScope) (frame_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
    change projectResult id ((applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr)) =
      (applyTerm p (frameSem ctx) cfg fuel ty t vs).run (st, tr) at framed
    rw [actual] at framed
    simp only [projectResult, id_eq] at framed
    have preserved := (frame_presAt p ctx cfg fuel).apply ty t vs st tr out next rules framed.symm
    have whole := congrArg (fun q => {q with base := base}) preserved
    have whole' : {next with base} = {st with base} := by simpa only [scheduling] using whole
    have eta : {next with base} = next := by rw [← baseEq]
    have nextEq : next = {st with base} := by rw [eta] at whole'; exact whole'
    rw [nextEq]

/-- The actual logical imm helper retains scheduling fields and emits
the existing pure template with its fresh destination. -/
theorem stock_logical_imm_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w k : Nat} {op : ALUOp} (width : w ≤ 64)
    (tag : ALUOp.ofIdx? k = some op) (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (imm : ImmLogic) :
    (applyTerm p (Stock.sem ctx) cfg (n + 20) 27 360 [.data 59 k [], .ty (.int w), .reg rx, .op (.immLogic imm)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2529.id) := by
  by_cases small : w ≤ 32
  · have legacy := alu_rr_imm_logic_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) tag (sz := .size32) rfl rx imm
    simpa only [szOf, small, ite_true] using pure_helper hp ctx hc (by decide : 360 ∈ aluScope) legacy
  · have legacy := alu_rr_imm_logic_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) tag (sz := .size64) rfl rx imm
    simpa only [szOf, small, ite_false] using pure_helper hp ctx hc (by decide : 360 ∈ aluScope) legacy

/-- The actual logical shift helper retains scheduling fields and emits
the existing pure template with its fresh destination. -/
theorem stock_logical_shift_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w k : Nat} {op : ALUOp} (width : w ≤ 64)
    (tag : ALUOp.ofIdx? k = some op) (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (ry : Reg) (shift : ShiftOpAndAmt) :
    (applyTerm p (Stock.sem ctx) cfg (n + 20) 27 377 [.data 59 k [], .ty (.int w), .reg rx, .reg ry, .op (.shiftOpAndAmt shift)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx ry shift)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2656.id) := by
  by_cases small : w ≤ 32
  · have legacy := alu_rrr_shift_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) tag (sz := .size32) rfl rx ry shift
    simpa only [szOf, small, ite_true] using pure_helper hp ctx hc (by decide : 377 ∈ aluScope) legacy
  · have legacy := alu_rrr_shift_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) tag (sz := .size64) rfl rx ry shift
    simpa only [szOf, small, ite_false] using pure_helper hp ctx hc (by decide : 377 ∈ aluScope) legacy

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

/-- Actual logical RHS3920 accounts for mapped requests, complete marking
state and immediate instruction emission. -/
theorem stock_rhs_3920 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {k w x : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {imm : ImmLogic}
    (tag : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_inst_3920.rhs (env5 (.data 59 k []) (.ty (.int w)) (.value x) (.int kk) (.op (.immLogic imm)))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark x with base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have helper := fun q trace fuel => stock_logical_imm_helper hp ctx hc width tag q trace fuel rx imm
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_inst_3920, stock_sem_ctor]
    rfl

/-- Actual logical RHS3923 accounts for mapped requests, complete marking
state and immediate instruction emission. -/
theorem stock_rhs_3923 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {k w y : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {imm : ImmLogic}
    (tag : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? y = some rx) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st y) (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_inst_3923.rhs (env5 (.data 59 k []) (.ty (.int w)) (.int kk) (.value y) (.op (.immLogic imm)))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark y with base := (st.base.fresh .int).2.emit (.aluRRImmLogic op (szOf w) (st.base.fresh .int).1 rx imm)}, trace) := by
  have xPut := stock_put_in_reg ctx st y rx hx safeX
  have helper := fun q trace fuel => stock_logical_imm_helper hp ctx hc width tag q trace fuel rx imm
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_inst_3923, stock_sem_ctor]
    rfl

/-- Actual logical RHS3928 accounts for mapped requests, complete marking
state and shifted-register instruction emission. -/
theorem stock_rhs_3928 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {k w x z : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {rz : Reg} {sh : ShiftOpAndAmt}
    (tag : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? x = some rx) (hz : ctx.valueReg? z = some rz) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeZ : DemandAllowed ctx st z) (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_inst_3928.rhs (env6 (.data 59 k []) (.ty (.int w)) (.value x) (.value z) (.int kk) (.op (.shiftOpAndAmt sh)))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {(st.mark x).mark z with base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx rz sh)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have zPut := stock_put_in_reg ctx (st.mark x) z rz hz safeZ
  have helper := fun q trace fuel => stock_logical_shift_helper hp ctx hc width tag q trace fuel rx rz sh
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_inst_3928, stock_sem_ctor]
    rfl

/-- Actual logical RHS3931 accounts for mapped requests, complete marking
state and shifted-register instruction emission. -/
theorem stock_rhs_3931 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {k w y z : Nat} {kk : Int} {op : ALUOp} {rx : Reg} {rz : Reg} {sh : ShiftOpAndAmt}
    (tag : ALUOp.ofIdx? k = some op) (hx : ctx.valueReg? y = some rx) (hz : ctx.valueReg? z = some rz) (width : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st y) (safeZ : DemandAllowed ctx st z) (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_inst_3931.rhs (env6 (.data 59 k []) (.ty (.int w)) (.value z) (.int kk) (.value y) (.op (.shiftOpAndAmt sh)))).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {(st.mark y).mark z with base := (st.base.fresh .int).2.emit (.aluRRRShift op (szOf w) (st.base.fresh .int).1 rx rz sh)}, trace) := by
  have xPut := stock_put_in_reg ctx st y rx hx safeX
  have zPut := stock_put_in_reg ctx (st.mark y) z rz hz safeZ
  have helper := fun q trace fuel => stock_logical_shift_helper hp ctx hc width tag q trace fuel rx rz sh
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_inst_3931, stock_sem_ctor]
    rfl

private def formImm (w : Nat) : ImmLogic := ⟨255, szOf w⟩
private def formShift : ShiftOpAndAmt := ⟨.lsl, 3⟩
private theorem formSafe (x : Nat) : DemandAllowed sinkCtx sinkState x := by
  intro i _
  change (#[false] : Array Bool)[i]! = false
  by_cases bound : i < 1
  · have equal : i = 0 := by omega
    subst i
    rfl
  · have outside : (#[false] : Array Bool).size ≤ i := Nat.le_of_not_lt bound
    rw [getElem!_def, Array.getElem?_eq_none outside]
    rfl

/-- Both widths inhabit the pure helpers and all four actual logical RHS
cases; immediates mark only the register operand and shifts mark both inputs. -/
theorem stock_logical_forms_witness (w : Nat) (supported : w = 32 ∨ w = 64) :
    ∃ (a b c d : State) (ta tb tc td : Array RuleId),
      (applyTerm program (Stock.sem sinkCtx) {} 20 27 360
        [.data 59 2 [], .ty (.int w), .reg (.vreg 192 .int), .op (.immLogic (formImm w))]).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),
            {sinkState with base := (sinkState.base.fresh .int).2.emit (.aluRRImmLogic .orr (szOf w) (.vreg 194 .int) (.vreg 192 .int) (formImm w))},
            (#[(if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)]).push rule_inst_2529.id) ∧
      (applyTerm program (Stock.sem sinkCtx) {} 20 27 377
        [.data 59 2 [], .ty (.int w), .reg (.vreg 192 .int), .reg (.vreg 193 .int), .op (.shiftOpAndAmt formShift)]).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),
            {sinkState with base := (sinkState.base.fresh .int).2.emit (.aluRRRShift .orr (szOf w) (.vreg 194 .int) (.vreg 192 .int) (.vreg 193 .int) formShift)},
            (#[(if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)]).push rule_inst_2656.id) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 40 rule_inst_3920.rhs
        (env5 (.data 59 2 []) (.ty (.int w)) (.value 0) (.int 255) (.op (.immLogic (formImm w))))).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),a,ta) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 40 rule_inst_3923.rhs
        (env5 (.data 59 2 []) (.ty (.int w)) (.int 255) (.value 1) (.op (.immLogic (formImm w))))).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),b,tb) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 40 rule_inst_3928.rhs
        (env6 (.data 59 2 []) (.ty (.int w)) (.value 0) (.value 1) (.int 3) (.op (.shiftOpAndAmt formShift)))).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),c,tc) ∧
      (evalExpr program (Stock.sem sinkCtx) {} 40 rule_inst_3931.rhs
        (env6 (.data 59 2 []) (.ty (.int w)) (.value 1) (.int 3) (.value 0) (.op (.shiftOpAndAmt formShift)))).run
          (sinkState,#[]) = .ok (some (.reg (.vreg 194 .int)),d,td) ∧
      a.demand[0]! = 1 ∧ a.demand[1]! = 0 ∧ b.demand[0]! = 0 ∧ b.demand[1]! = 1 ∧
      c.demand = #[1,1] ∧ d.demand = #[1,1] ∧
      a.base.emitted = #[.aluRRImmLogic .orr (szOf w) (.vreg 194 .int) (.vreg 192 .int) (formImm w)] ∧
      c.base.emitted = #[.aluRRRShift .orr (szOf w) (.vreg 194 .int) (.vreg 192 .int) (.vreg 193 .int) formShift] := by
  have width : w ≤ 64 := by rcases supported with rfl | rfl <;> decide
  have helperImm := stock_logical_imm_helper data_program sinkCtx (cfg := {}) rfl width
    (k := 2) (op := .orr) rfl sinkState #[] 0 (.vreg 192 .int) (formImm w)
  have helperShift := stock_logical_shift_helper data_program sinkCtx (cfg := {}) rfl width
    (k := 2) (op := .orr) rfl sinkState #[] 0 (.vreg 192 .int) (.vreg 193 .int) formShift
  obtain ⟨ta, ha⟩ := stock_rhs_3920 data_program sinkCtx (cfg := {}) rfl (k := 2) (op := .orr)
    (kk := 255) rfl (x := 0) (rx := .vreg 192 .int) rfl width sinkState (formSafe 0) #[] 0 (imm := formImm w)
  obtain ⟨tb, hb⟩ := stock_rhs_3923 data_program sinkCtx (cfg := {}) rfl (k := 2) (op := .orr)
    (kk := 255) rfl (y := 1) (rx := .vreg 193 .int) rfl width sinkState (formSafe 1) #[] 0 (imm := formImm w)
  obtain ⟨tc, hc⟩ := stock_rhs_3928 data_program sinkCtx (cfg := {}) rfl (k := 2) (op := .orr)
    (kk := 3) rfl (x := 0) (z := 1) (rx := .vreg 192 .int) (rz := .vreg 193 .int) rfl rfl width
    sinkState (formSafe 0) (formSafe 1) #[] 0 (sh := formShift)
  obtain ⟨td, hd⟩ := stock_rhs_3931 data_program sinkCtx (cfg := {}) rfl (k := 2) (op := .orr)
    (kk := 3) rfl (y := 0) (z := 1) (rx := .vreg 192 .int) (rz := .vreg 193 .int) rfl rfl width
    sinkState (formSafe 0) (formSafe 1) #[] 0 (sh := formShift)
  exact ⟨_,_,_,_,ta,tb,tc,td,helperImm,helperShift,ha,hb,hc,hd,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end Backend.Stock.Proof.LogicalForms

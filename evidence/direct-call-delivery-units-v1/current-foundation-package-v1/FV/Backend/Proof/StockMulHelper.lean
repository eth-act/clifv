import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.IselTermsALUAMul
namespace Backend.Stock.Proof.ScalarMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def helperScope : List Nat := [111, 113, 175, 201, 235, 305, 362, 382, 443, 444, 451, 452, 1820, 1821, 1973, 1974, 1985, 1986, 2028, 2029]
private theorem helper_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx)
      (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [helperScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t111] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t113] at lookup
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
    · rw [hp.t382] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t443] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t444] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t451] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t452] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1820] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1821] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1973] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1974] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1985] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1986] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2028] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t2029] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
  · intro t term member lookup flags ex kind r recorded
    simp only [helperScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp.t111] at lookup
      cases lookup
      cases kind
    · rw [hp.t113] at lookup
      cases lookup
      cases kind
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
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_1592, rule_inst_1593]
    · rw [hp.t362] at lookup
      cases lookup
      rw [hp.r362] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_2545]
    · rw [hp.t382] at lookup
      cases lookup
      rw [hp.r382] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_2701]
    · rw [hp.t443] at lookup
      cases lookup
      rw [hp.r443] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_3177]
    · rw [hp.t444] at lookup
      cases lookup
      rw [hp.r444] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_3182]
    · rw [hp.t451] at lookup
      cases lookup
      rw [hp.r451] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_3213]
    · rw [hp.t452] at lookup
      cases lookup
      rw [hp.r452] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_3218]
    · rw [hp.t1820] at lookup
      cases lookup
      cases kind
    · rw [hp.t1821] at lookup
      cases lookup
      cases kind
    · rw [hp.t1973] at lookup
      cases lookup
      cases kind
    · rw [hp.t1974] at lookup
      cases lookup
      cases kind
    · rw [hp.t1985] at lookup
      cases lookup
      cases kind
    · rw [hp.t1986] at lookup
      cases lookup
      cases kind
    · rw [hp.t2028] at lookup
      cases lookup
      cases kind
    · rw [hp.t2029] at lookup
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
    ProjectionScope p (frameSem ctx) id (Stock.externCtor ctx) (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    have unchanged : term.id ∉ revisedCtors := by
      simp only [helperScope, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hp.t111] at lookup
        cases lookup
        decide
      · rw [hp.t113] at lookup
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
      · rw [hp.t382] at lookup
        cases lookup
        decide
      · rw [hp.t443] at lookup
        cases lookup
        decide
      · rw [hp.t444] at lookup
        cases lookup
        decide
      · rw [hp.t451] at lookup
        cases lookup
        decide
      · rw [hp.t452] at lookup
        cases lookup
        decide
      · rw [hp.t1820] at lookup
        cases lookup
        decide
      · rw [hp.t1821] at lookup
        cases lookup
        decide
      · rw [hp.t1973] at lookup
        cases lookup
        decide
      · rw [hp.t1974] at lookup
        cases lookup
        decide
      · rw [hp.t1985] at lookup
        cases lookup
        decide
      · rw [hp.t1986] at lookup
        cases lookup
        decide
      · rw [hp.t2028] at lookup
        cases lookup
        decide
      · rw [hp.t2029] at lookup
        cases lookup
        decide
    change projectCtor id (Stock.externCtor ctx term vs st) = frameCtor ctx term vs st
    rw [stock_ctor_baseOnly _ _ _ _ unchanged]
    unfold frameCtor
    cases Backend.externCtor ctx term vs st.base with
    | ok pair => cases pair; rfl
    | fail => rfl
    | unmodeled e => rfl
  · exact (helper_scope hp ctx).rules

private theorem pure_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {fuel ty t : Nat} {vs : List V} (allowed : t ∈ helperScope)
    {st : State} {base : LState} {tr trace : Array RuleId} {v : Option V}
    (legacy : (applyTerm p (Backend.sem ctx) cfg fuel ty t vs).run (st.base, tr) = .ok (v, base, trace)) :
    (applyTerm p (Stock.sem ctx) cfg fuel ty t vs).run (st, tr) =
      .ok (v, {st with base}, trace) := by
  have projection := (evaluation_scoped_restate p (Backend.sem ctx) cfg hc State.base
    (Stock.externCtor ctx) (fun t v st => Backend.externExtract ctx t v st.base)
    (fun t => t ∈ helperScope) (helper_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
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
      (fun t => t ∈ helperScope) (frame_scope hp ctx) (fun _ _ _ => rfl) fuel).term ty t vs allowed st tr
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


/-- The actual four-register ALU helper changes only the base lowering state;
all Stock scheduling fields survive the complete generated helper execution. -/
theorem stock_mul_rrrr_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w k : Nat} {op : ALUOp3}
    (width : w ≤ 64) (tag : ALUOp3.ofIdx? k = some op)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry rz : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+20) 27 382
      [.data 60 k [],.ty (.int w),.reg rx,.reg ry,.reg rz]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRR op (szOf w) (st.base.fresh .int).1 rx ry rz)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2701.id) := by
  by_cases small : w ≤ 32
  · have legacy := alu_rrrr_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) tag (sz := .size32) rfl rx ry rz
    simpa only [szOf,small,ite_true] using pure_helper hp ctx hc (by decide : 382 ∈ helperScope) legacy
  · have legacy := alu_rrrr_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) tag (sz := .size64) rfl rx ry rz
    simpa only [szOf,small,ite_false] using pure_helper hp ctx hc (by decide : 382 ∈ helperScope) legacy

/-- Actual MADD helper emission preserves Stock scheduling and uses its original
operand-size selection and trace, without a projection premise from the caller. -/
theorem stock_madd_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry rz : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+30) 27 443 [.ty (.int w),.reg rx,.reg ry,.reg rz]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRR .mAdd (szOf w) (st.base.fresh .int).1 rx ry rz)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2701.id).push rule_inst_3177.id) := by
  by_cases small : w ≤ 32
  · have legacy := madd_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) (sz := .size32) rfl rx ry rz
    simpa only [szOf,small,ite_true] using pure_helper hp ctx hc (by decide : 443 ∈ helperScope) legacy
  · have legacy := madd_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) (sz := .size64) rfl rx ry rz
    simpa only [szOf,small,ite_false] using pure_helper hp ctx hc (by decide : 443 ∈ helperScope) legacy

/-- Actual MSUB helper emission preserves Stock scheduling and uses its original
operand-size selection and trace, without a projection premise from the caller. -/
theorem stock_msub_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry rz : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+30) 27 444 [.ty (.int w),.reg rx,.reg ry,.reg rz]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRR .mSub (szOf w) (st.base.fresh .int).1 rx ry rz)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2701.id).push rule_inst_3182.id) := by
  by_cases small : w ≤ 32
  · have legacy := msub_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) (sz := .size32) rfl rx ry rz
    simpa only [szOf,small,ite_true] using pure_helper hp ctx hc (by decide : 444 ∈ helperScope) legacy
  · have legacy := msub_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) (sz := .size64) rfl rx ry rz
    simpa only [szOf,small,ite_false] using pure_helper hp ctx hc (by decide : 444 ∈ helperScope) legacy

end Backend.Stock.Proof.ScalarMul

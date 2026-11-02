import FV.Backend.Proof.StockProjection
import FV.Arm.MinTheory
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.IselRulesALU
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.IselTermsAluB
namespace Backend.Stock.Proof.ScalarShift
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def helperScope : List Nat := [111, 113, 175, 201, 235, 305, 360, 361, 417, 502, 1823, 1824, 1846, 1966, 2028, 2029]
private theorem helper_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx)
      (fun t => t ∈ helperScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [helperScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [hp.t360] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t361] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t417] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t502] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1823] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1824] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1846] at lookup
      cases lookup
      exact stock_ctor_unchanged ctx _ vs st (by decide)
    · rw [hp.t1966] at lookup
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
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [hp.t360] at lookup
      cases lookup
      rw [hp.r360] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_2529]
    · rw [hp.t361] at lookup
      cases lookup
      rw [hp.r361] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_2537]
    · rw [hp.t417] at lookup
      cases lookup
      rw [hp.r417] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_2991]
    · rw [hp.t502] at lookup
      cases lookup
      rw [hp.r502] at recorded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at recorded
      rcases recorded with rfl
      all_goals simp [RuleScoped, IfLetsScoped, ExprScoped, exprCalls, argCalls, bindCalls, helperScope, rule_inst_3431]
    · rw [hp.t1823] at lookup
      cases lookup
      cases kind
    · rw [hp.t1824] at lookup
      cases lookup
      cases kind
    · rw [hp.t1846] at lookup
      cases lookup
      cases kind
    · rw [hp.t1966] at lookup
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
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [hp.t360] at lookup
        cases lookup
        decide
      · rw [hp.t361] at lookup
        cases lookup
        decide
      · rw [hp.t417] at lookup
        cases lookup
        decide
      · rw [hp.t502] at lookup
        cases lookup
        decide
      · rw [hp.t1823] at lookup
        cases lookup
        decide
      · rw [hp.t1824] at lookup
        cases lookup
        decide
      · rw [hp.t1846] at lookup
        cases lookup
        decide
      · rw [hp.t1966] at lookup
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


/-- Actual immediate-shift helper emission retains the complete Stock
scheduling state and the original operand-size selection. -/
theorem stock_shift_imm_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w k : Nat} {op : ALUOp}
    (width : w ≤ 64) (tag : ALUOp.ofIdx? k = some op)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (amt : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+20) 27 361 [.data 59 k [],.ty (.int w),.reg rx,.op (.immShift amt)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmShift op (szOf w) (st.base.fresh .int).1 rx amt)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2537.id) := by
  by_cases small : w ≤ 32
  · have legacy := alu_rr_imm_shift_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) tag (sz := .size32) rfl rx amt
    simpa only [szOf,small,ite_true] using pure_helper hp ctx hc (by decide : 361 ∈ helperScope) legacy
  · have legacy := alu_rr_imm_shift_run hp ctx hc st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) width) tag (sz := .size64) rfl rx amt
    simpa only [szOf,small,ite_false] using pure_helper hp ctx hc (by decide : 361 ∈ helperScope) legacy

/-- Actual extension-helper emission changes only the base state, preserving
all scheduling fields while allocating exactly one fresh integer register. -/
theorem stock_extend_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    (rx : Reg) (sg : Bool) (sourceWidth to : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+20) 27 417 [.reg rx,.bool sg,.int sourceWidth,.int to]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx sg sourceWidth to)},tr.push rule_inst_2991.id) := by
  exact pure_helper hp ctx hc (by decide : 417 ∈ helperScope) (extend_run hp ctx hc st.base tr n rx sg sourceWidth to)

/-- A successful actual extension-helper call has precisely the same fresh
output and full-state behavior as its forward contract. -/
theorem stock_extend_helper_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {st next : State} {tr trace : Array RuleId} {n : Nat}
    {rx : Reg} {sg : Bool} {sourceWidth to : Nat} {out : V}
    (run : (applyTerm p (Stock.sem ctx) cfg (n+20) 27 417 [.reg rx,.bool sg,.int sourceWidth,.int to]).run
      (st,tr) = .ok (some out,next,trace)) :
    out = .reg (st.base.fresh .int).1 ∧
      next = {st with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx sg sourceWidth to)} := by
  rw [stock_extend_helper hp ctx hc st tr n rx sg sourceWidth to] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩

end Backend.Stock.Proof.ScalarShift

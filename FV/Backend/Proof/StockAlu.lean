import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselScopedProjection
import FV.Backend.Proof.IselFlowGen
import FV.Backend.Proof.IselRulesALU
import FV.Backend.Proof.IselFamily
import FV.Backend.Proof.StockAliasSemantics

/-! Actual Stock add/subtract roots reuse the existing pure ALU helper semantics.
Operand constructors retain mapped registers while recording selected-code demand. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private def aluScope : List Nat := [164, 170, 172, 175, 201, 235, 305, 362, 432, 437, 1820, 1962, 1963, 2028, 2029]
private theorem alu_scope {p : Program} (hp : Data p) (ctx : Ctx) :
    ProjectionScope p (Backend.sem ctx) State.base (Stock.externCtor ctx)
      (fun t => t ∈ aluScope) := by
  constructor
  · intro t term member lookup vs st
    simp only [aluScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro t term member lookup flags ex kind r recorded
    simp only [aluScope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- The shared register ALU helper retains every Stock scheduling field and
emits the existing helper template for any supported operation tag. -/
theorem stock_alu_rrr_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w k : Nat} {op : ALUOp}
    (hw : w ≤ 64) (hk : ALUOp.ofIdx? k = some op)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n + 20) 27 362 [.data 59 k [], .ty (.int w), .reg rx, .reg ry]).run
      (st, tr) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR op (szOf w) (st.base.fresh .int).1 rx ry)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id) := by
  by_cases small : w ≤ 32
  · have legacy := alu_rrr_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small)
      (fun base rd rn rm => emit_aluRRR ctx base hk (sz := .size32) rfl rd rn rm) rx ry
    simpa only [szOf, small, ite_true] using pure_helper hp ctx hc (by decide : 362 ∈ aluScope) legacy
  · have legacy := alu_rrr_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) hw)
      (fun base rd rn rm => emit_aluRRR ctx base hk (sz := .size64) rfl rd rn rm) rx ry
    simpa only [szOf, small, ite_false] using pure_helper hp ctx hc (by decide : 362 ∈ aluScope) legacy

private theorem add_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w : Nat} (hw : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n + 30) 27 432 [.ty (.int w), .reg rx, .reg ry]).run
      (st, tr) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR .add (szOf w) (st.base.fresh .int).1 rx ry)}, ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3118.id) := by
  by_cases small : w ≤ 32
  · have legacy := add_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small) (emit_add_32 ctx) rx ry
    simpa only [szOf, small, ite_true] using pure_helper hp ctx hc (by decide : 432 ∈ aluScope) legacy
  · have legacy := add_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) hw) (emit_add_64 ctx) rx ry
    simpa only [szOf, small, ite_false] using pure_helper hp ctx hc (by decide : 432 ∈ aluScope) legacy
private theorem sub_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {w : Nat} (hw : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n + 30) 27 437 [.ty (.int w), .reg rx, .reg ry]).run
      (st, tr) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 rx ry)}, ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3138.id) := by
  by_cases small : w ≤ 32
  · have legacy := sub_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx hc base trace fuel small)
      (fun base rd rn rm => emit_aluRRR ctx base (op := .sub) (sz := .size32) rfl rfl rd rn rm) rx ry
    simpa only [szOf, small, ite_true] using pure_helper hp ctx hc (by decide : 437 ∈ aluScope) legacy
  · have legacy := sub_run hp ctx hc (w := w) st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx hc base trace fuel (by omega) hw)
      (fun base rd rn rm => emit_aluRRR ctx base (op := .sub) (sz := .size64) rfl rfl rd rn rm) rx ry
    simpa only [szOf, small, ite_false] using pure_helper hp ctx hc (by decide : 437 ∈ aluScope) legacy
private theorem output_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n + 10) 25 172 [.reg r]).run (st, tr) =
      .ok (some (.regsVec [[r]]), st, tr.push rule_prelude_lower_105.id) := by
  exact pure_helper hp ctx hc (by decide : 172 ∈ aluScope) (output_reg_run hp ctx hc st.base tr n r)

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl

private theorem stock_sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem stock_sem_unData (ctx : Ctx) (ty t k : Nat) (fs : List V) :
    (Stock.sem ctx).unData ty (.data t k fs) = if t = ty then some (k, fs) else none :=
  sem_unData ctx ty t k fs

/-- The actual Stock add root matches the original instruction data and retains
all scheduling fields; mapping source values to dense registers does not affect matching. -/
theorem stock_match_86 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n + 2) rule_lower_86 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), st, tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data, type, Option.getD_some] at extraction
  cases hp
  isel_eval [*, rule_lower_86, stock_sem_extract, stock_sem_unData,
    ext_ty_int_ref_scalar_64_extract ctx st.base width, ext_value_array_2]

/-- Matching the Stock subtraction root has the same state/frame behavior. -/
theorem stock_match_801 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    {i x y w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (width : w ≤ 64)
    (data : info.data = .data 152 2 [.data 151 74 [], .values [x, y]])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) cfg (n + 2) rule_lower_801 [.inst i]).run (st, tr) =
      .ok (some (env3 (.ty (.int w)) (.value x) (.value y)), st, tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data, type, Option.getD_some] at extraction
  cases hp
  isel_eval [*, rule_lower_801, stock_sem_extract, stock_sem_unData,
    ext_ty_int_ref_scalar_64_extract ctx st.base width, ext_value_array_2]

/-- The actual Stock add root marks both operands and emits the saved ALU helper
code using their mapped registers, without assuming source IDs are vreg numbers. -/
theorem stock_rhs_86 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w : Nat} {rx ry : Reg}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_86.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR .add (szOf w) (st.base.fresh .int).1 rx ry)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have yPut := stock_put_in_reg ctx (st.mark x) y ry hy safeY
  have addRun := fun q trace fuel => add_helper hp ctx hc (w := w) hw q trace fuel rx ry
  have outputRun := fun q trace fuel r => output_helper hp ctx hc q trace fuel r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_lower_86, stock_sem_ctor]
    rfl

/-- The actual Stock subtraction root has the same operand-demand bookkeeping. -/
theorem stock_rhs_801 {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {x y w : Nat} {rx ry : Reg}
    (hx : ctx.valueReg? x = some rx) (hy : ctx.valueReg? y = some ry) (hw : w ≤ 64)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace, (evalExpr p (Stock.sem ctx) cfg (n + 40) rule_lower_801.rhs
      (env3 (.ty (.int w)) (.value x) (.value y))).run (st, tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark y with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 rx ry)}, trace) := by
  have xPut := stock_put_in_reg ctx st x rx hx safeX
  have yPut := stock_put_in_reg ctx (st.mark x) y ry hy safeY
  have subRun := fun q trace fuel => sub_helper hp ctx hc (w := w) hw q trace fuel rx ry
  have outputRun := fun q trace fuel r => output_helper hp ctx hc q trace fuel r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*, rule_lower_801, stock_sem_ctor]
    rfl

/-- The saved ALU template executes through mapped, alias-resolved operands.
It covers add/subtract/and/or/xor at every supported integer width and changes
only the fresh destination, independently of source IDs or allocation order. -/
theorem stock_alu_rrr_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {op : ALUOp} {cop : Clif.BinaryOp}
    (operation : (op, cop) = (.add, .iadd) ∨ (op, cop) = (.sub, .isub) ∨
      (op, cop) = (.and, .band) ∨ (op, cop) = (.orr, .bor) ∨ (op, cop) = (.eor, .bxor))
    {ty : Clif.Ty} (width : ty.width ≤ 64) {ctx : Ctx} {fr : Clif.Frame}
    {aliases : Array (Option Nat)} {ρ : Nat → CV} {x y nx ny d : Nat}
    (bounded : aliases.size ≤ d)
    (mappedX : ctx.valueReg? x = some (.vreg nx .int))
    (mappedY : ctx.valueReg? y = some (.vreg ny .int))
    (held : ValuesHeld (fun z => z = x ∨ z = y) ctx fr (fun k => ρ (aliasNum aliases k)))
    {u v : BitVec ty.width} (sourceX : fr.getAs x ty = .ok u) (sourceY : fr.getAs y ty = .ok v) :
    ∃ ρ', PRun F isem
        [(MInst.aluRRR op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size + 1))] ρ ρ' ∧
      VHolds ⟨ty, Clif.Sem.binary cop u v⟩ (ρ' d) ∧
      ∀ n, n ≠ d → ρ' n = ρ n := by
  have xValue := held.read (Or.inl rfl) (getAs_ok sourceX) mappedX
  have yValue := held.read (Or.inr rfl) (getAs_ok sourceY) mappedY
  obtain ⟨r, computed, value⟩ := aluVal_holds operation (szOf_bits width) xValue yValue
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have destination : Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int) =
      .vreg d .int := by
    rw [resolve_vreg]
    change Reg.vreg (aliasNum aliases d) .int = _
    rw [fresh]
  have code : (MInst.aluRRR op (szOf ty.width) (.vreg d .int) (.vreg nx .int) (.vreg ny .int)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size + 1)) =
      .aluRRR op (szOf ty.width) (.vreg d .int) (.vreg (aliasNum aliases nx) .int) (.vreg (aliasNum aliases ny) .int) := by
    change MInst.aluRRR op (szOf ty.width)
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg d .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg nx .int))
      (Backend.lowerFunction.resolve aliases (aliases.size + 1) (.vreg ny .int)) = _
    rw [destination, resolve_vreg, resolve_vreg]
    rfl
  refine ⟨upd ρ d (resX (szOf ty.width) r), ?_, ?_, ?_⟩
  · intro w
    obtain ⟨w', executed, world⟩ := seqRun_aluRRR refines (d := d) (w := w) computed
    exact ⟨w', by simpa only [code] using executed, world⟩
  · rw [upd_same]
    exact value
  · intro n different
    simp only [upd, different, ite_false]

attribute [local semireducible] Isle.Aarch64.program

private def exampleFunction (subtract : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_alu_sparse"
  sig := { params := [⟨ty, .none, .normal⟩, ⟨ty, .none, .normal⟩], returns := [⟨ty, .none, .normal⟩], callConv := some .systemV }
  blocks := [{ id := 0, params := [(7, ty), (31, ty)], body := [⟨[100], .binary (if subtract then .isub else .iadd) ty 7 31⟩], term := .ret [100] }] }
private def exampleBuilt (subtract : Bool) (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (exampleFunction subtract ty)).toOption.getD (sinkCtx, #[], sinkState)
private def exampleCtx (subtract : Bool) (ty : Clif.Ty) : Ctx := (exampleBuilt subtract ty).1
private def exampleState : State := {sinkState with
  base := ⟨195, Array.replicate 195 .int, #[], 0⟩
  demand := (Array.replicate 101 0).set! 100 1
  sunk := #[] }
private def exampleFrame (subtract : Bool) (ty : Clif.Ty) : Clif.Frame := {
  func := exampleFunction subtract ty
  regs := fun x => if x = 7 then some (.ofInt ty 7) else if x = 31 then some (.ofInt ty 5) else none
  slots := [], body := [], term := .ret [100] }
private def exampleRegs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private theorem exampleSafe (ctx : Ctx) (x : Nat) : DemandAllowed ctx exampleState x := by
  intro i _
  change (#[] : Array Bool)[i]! = false
  simp
private theorem exampleSelfRefines : Refines (fun _ => True) ispec :=
  fun _ _ _ _ w' _ h => ⟨w', h, SameWorld.refl _ _⟩

private theorem exampleFacts (subtract : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    Stock.buildCtx (exampleFunction subtract ty) = .ok (exampleBuilt subtract ty) ∧
      (exampleCtx subtract ty).insts[0]? = some (exampleCtx subtract ty).insts[0]! ∧
      (exampleCtx subtract ty).insts[0]!.clif = some (.binary (if subtract then .isub else .iadd) ty 7 31) ∧
      (exampleCtx subtract ty).insts[0]!.resTys.head? = some (.int ty.width) ∧
      (exampleCtx subtract ty).insts[0]!.data = .data 152 2 [.data 151 (if subtract then 74 else 73) [], .values [7, 31]] ∧
      (exampleCtx subtract ty).valueReg? 7 = some (.vreg 192 .int) ∧
      (exampleCtx subtract ty).valueReg? 31 = some (.vreg 193 .int) ∧
      (exampleCtx subtract ty).valueReg? 100 = some (.vreg 194 .int) := by
  rcases supported with rfl | rfl <;> cases subtract
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
private theorem exampleHeld (subtract : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    ValuesHeld (fun z => z = 7 ∨ z = 31) (exampleCtx subtract ty) (exampleFrame subtract ty)
      (fun k => exampleRegs (aliasNum #[] k)) := by
  obtain ⟨_, _, _, _, _, xMap, yMap, _⟩ := exampleFacts subtract ty supported
  intro z required val lookup
  rcases required with rfl | rfl
  · change some (Clif.Val.ofInt ty 7) = some val at lookup
    cases lookup
    refine ⟨192, xMap, ?_⟩
    change VHolds (.ofInt ty 7) 7
    rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
  · change some (Clif.Val.ofInt ty 5) = some val at lookup
    cases lookup
    refine ⟨193, yMap, ?_⟩
    change VHolds (.ofInt ty 5) 5
    rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel

/-- Real sparse-ID context construction, matching and RHS execution at both
32- and64-bit widths: source7/31 maps192/193, result100 maps194, and fresh195
computes12 for add or2 for subtraction while both source demands become1. -/
theorem stock_alu_roots_witness (subtract : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (ctx : Ctx) (info : IInfo) (next : State) (trace : Array RuleId) (ρ' : Nat → CV),
      Stock.buildCtx (exampleFunction subtract ty) = .ok (exampleBuilt subtract ty) ∧
      ctx = exampleCtx subtract ty ∧ ctx.insts[0]? = some info ∧
      info.clif = some (.binary (if subtract then .isub else .iadd) ty 7 31) ∧
      ctx.valueReg? 7 = some (.vreg 192 .int) ∧ ctx.valueReg? 31 = some (.vreg 193 .int) ∧
      ctx.valueReg? 100 = some (.vreg 194 .int) ∧
      (matchRule program (Stock.sem ctx) {} 2 (if subtract then rule_lower_801 else rule_lower_86) [.inst 0]).run
        (exampleState, #[]) = .ok (some (env3 (.ty (.int ty.width)) (.value 7) (.value 31)), exampleState, #[]) ∧
      (evalExpr program (Stock.sem ctx) {} 40 (if subtract then rule_lower_801 else rule_lower_86).rhs
        (env3 (.ty (.int ty.width)) (.value 7) (.value 31))).run (exampleState, #[]) =
          .ok (some (.regsVec [[.vreg 195 .int]]), next, trace) ∧
      next.base.emitted = #[.aluRRR (if subtract then .sub else .add) (szOf ty.width)
        (.vreg 195 .int) (.vreg 192 .int) (.vreg 193 .int)] ∧
      next.demand[7]! = 1 ∧ next.demand[31]! = 1 ∧ next.demand[100]! = 1 ∧
      PRun (fun _ => True) ispec next.base.emitted.toList exampleRegs ρ' ∧
      VHolds (.ofInt ty (if subtract then 2 else 12)) (ρ' 195) ∧ ρ' 192 = 7 ∧ ρ' 193 = 5 := by
  obtain ⟨build, source, original, type, data, xMap, yMap, resultMap⟩ := exampleFacts subtract ty supported
  have width : ty.width ≤ 64 := by rcases supported with rfl | rfl <;> decide
  have xSource : (exampleFrame subtract ty).getAs 7 ty = .ok (BitVec.ofInt ty.width 7) := by
    rcases supported with rfl | rfl <;> rfl
  have ySource : (exampleFrame subtract ty).getAs 31 ty = .ok (BitVec.ofInt ty.width 5) := by
    rcases supported with rfl | rfl <;> rfl
  cases subtract with
  | false =>
    have matched := stock_match_86 data_program (exampleCtx false ty) (cfg := {}) source type width data exampleState #[] 0
    obtain ⟨trace, evaluated⟩ := stock_rhs_86 data_program (exampleCtx false ty) (cfg := {}) rfl xMap yMap width
      exampleState (exampleSafe _ 7) (exampleSafe _ 31) #[] 0
    obtain ⟨ρ', executed, value, kept⟩ := stock_alu_rrr_resolved exampleSelfRefines (Or.inl rfl) width
      (aliases := #[]) (ρ := exampleRegs) (d := 195) (by decide) xMap yMap
      (exampleHeld false ty supported) xSource ySource
    have literal : (⟨ty, Clif.Sem.binary .iadd (BitVec.ofInt ty.width 7) (BitVec.ofInt ty.width 5)⟩ : Clif.Val) =
        .ofInt ty 12 := by rcases supported with rfl | rfl <;> decide +kernel
    refine ⟨_, _, _, trace, ρ', build, rfl, source, original, xMap, yMap, resultMap, matched, evaluated,
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simpa [exampleState, State.mark, LState.fresh, LState.emit, MInst.mapRegs,
        Backend.lowerFunction.resolve, chaseF] using executed
    · change VHolds (.ofInt ty 12) (ρ' 195)
      rw [← literal]; exact value
    · exact (kept 192 (by decide)).trans rfl
    · exact (kept 193 (by decide)).trans rfl
  | true =>
    have matched := stock_match_801 data_program (exampleCtx true ty) (cfg := {}) source type width data exampleState #[] 0
    obtain ⟨trace, evaluated⟩ := stock_rhs_801 data_program (exampleCtx true ty) (cfg := {}) rfl xMap yMap width
      exampleState (exampleSafe _ 7) (exampleSafe _ 31) #[] 0
    obtain ⟨ρ', executed, value, kept⟩ := stock_alu_rrr_resolved exampleSelfRefines (Or.inr (Or.inl rfl)) width
      (aliases := #[]) (ρ := exampleRegs) (d := 195) (by decide) xMap yMap
      (exampleHeld true ty supported) xSource ySource
    have literal : (⟨ty, Clif.Sem.binary .isub (BitVec.ofInt ty.width 7) (BitVec.ofInt ty.width 5)⟩ : Clif.Val) =
        .ofInt ty 2 := by rcases supported with rfl | rfl <;> decide +kernel
    refine ⟨_, _, _, trace, ρ', build, rfl, source, original, xMap, yMap, resultMap, matched, evaluated,
      rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simpa [exampleState, State.mark, LState.fresh, LState.emit, MInst.mapRegs,
        Backend.lowerFunction.resolve, chaseF] using executed
    · change VHolds (.ofInt ty 2) (ρ' 195)
      rw [← literal]; exact value
    · exact (kept 192 (by decide)).trans rfl
    · exact (kept 193 (by decide)).trans rfl

end Backend.Stock.Proof

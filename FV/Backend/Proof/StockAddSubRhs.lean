import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.IselTermsALUAExt
import FV.Backend.Proof.StockImm12Helper
import FV.Backend.Proof.StockAddSubPure
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State)
    (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]
theorem stock_addsub_shift_helper {p : Program} (hp : Data p) (ctx : Ctx) (subtract : Bool)
    {w : Nat} (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx rz : Reg) (sh : ShiftOpAndAmt) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 (if subtract then 440 else 435)
      [.ty (.int w),.reg rx,.reg rz,.op (.shiftOpAndAmt sh)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRShift (if subtract then .sub else .add)
          (szOf w) (st.base.fresh .int).1 rx rz sh)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2656.id).push
          (if subtract then rule_inst_3150.id else rule_inst_3130.id)) := by
  have inner := fun q trace fuel => LogicalForms.stock_logical_shift_helper hp ctx (cfg := {}) rfl width
    (k := if subtract then 1 else 0) (op := if subtract then .sub else .add)
    (by cases subtract <;> rfl) q trace fuel rx rz sh
  cases hp
  cases subtract
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*,rule_inst_3130,rule_inst_3150,sem_mkData]
  all_goals rfl
theorem stock_addsub_imm_helper {p : Program} (hp : Data p) (ctx : Ctx) (subtract : Bool)
    {w : Nat} (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (imm : Imm12) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 (if subtract then 438 else 433)
      [.ty (.int w),.reg rx,.op (.imm12 imm)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImm12 (if subtract then .sub else .add)
          (szOf w) (st.base.fresh .int).1 rx imm)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2648.id).push
          (if subtract then rule_inst_3142.id else rule_inst_3122.id)) := by
  have inner := fun q trace fuel => ScalarCount.stock_alu_imm12_helper hp ctx (cfg := {}) rfl width
    (k := if subtract then 1 else 0) (op := if subtract then .sub else .add)
    (by cases subtract <;> rfl) q trace fuel rx imm
  cases hp
  cases subtract
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*,rule_inst_3122,rule_inst_3142,sem_mkData]
  all_goals rfl
def shiftRule (subtract left : Bool) : Rule :=
  if subtract then rule_lower_821 else if left then rule_lower_120 else rule_lower_116
def shiftEnv (left : Bool) (w x z y : Nat) (c : Int) (sh : ShiftOpAndAmt) : Isle.Interp.Env V :=
  if left then env5 (.ty (.int w)) (.value z) (.int c) (.value x) (.op (.shiftOpAndAmt sh))
  else env5 (.ty (.int w)) (.value x) (.value z) (.int c) (.op (.shiftOpAndAmt sh))
/-- The actual fused-shift roots request only the unshifted operand and the
original shifted source, retain all scheduling fields and emit one instruction. -/
theorem stock_addsub_shift_rhs {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x z y : Nat} (width : w ≤ 64) (c : Int) (sh : ShiftOpAndAmt)
    {rx rz : Reg} (mapX : ctx.valueReg? x = some rx) (mapZ : ctx.valueReg? z = some rz)
    (st : State) (safeX : DemandAllowed ctx st x) (safeZ : DemandAllowed ctx st z) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+60) (shiftRule subtract left).rhs
      (shiftEnv left w x z y c sh)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark z with base := ((st.base.fresh .int).2.emit
          (.aluRRRShift (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx rz sh))},trace) := by
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  have requestZ := stock_put_in_reg ctx (st.mark x) z rz mapZ safeZ
  have helper := fun q trace fuel => stock_addsub_shift_helper hp ctx subtract width q trace fuel rx rz sh
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases subtract <;> cases left
  · refine Exists.intro ?traceAddRight ?proofAddRight
    case proofAddRight =>
      simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_116,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceAddLeft ?proofAddLeft
    case proofAddLeft =>
      simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_120,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceSub ?proofSub
    case proofSub =>
      simp only [shiftRule,shiftEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_821,sem_ctor,sem_mkData]
      all_goals rfl
  · cases side rfl
theorem stock_addsub_extend_reg {p : Program} (hp : Data p) (ctx : Ctx) (subtract : Bool)
    {w : Nat} (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx rz : Reg) (e : ExtendOp) :
    (applyTerm p (Stock.sem ctx) {} (n+20) 27 380
      [.data 59 (if subtract then 1 else 0) [],.ty (.int w),.reg rx,.reg rz,.data 84 e.idx []]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRRExtend (if subtract then .sub else .add)
          (szOf w) (st.base.fresh .int).1 rx rz e)},
        (tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2684.id) := by
  have tag : ALUOp.ofIdx? (if subtract then 1 else 0) = some (if subtract then .sub else .add) := by cases subtract <;> rfl
  by_cases small : w ≤ 32
  · have legacy := alu_rrr_extend_run hp ctx (cfg := {}) rfl st.base tr n
      (fun base trace fuel => operand_size_32 hp ctx (cfg := {}) rfl base trace fuel small)
      tag (sz := .size32) rfl rx rz e
    simpa only [szOf,small,ite_true] using stock_addsub_pure_helper hp ctx (cfg := {}) rfl (by decide) legacy
  · have legacy := alu_rrr_extend_run hp ctx (cfg := {}) rfl st.base tr n
      (fun base trace fuel => operand_size_64 hp ctx (cfg := {}) rfl base trace fuel (by omega) width)
      tag (sz := .size64) rfl rx rz e
    simpa only [szOf,small,ite_false] using stock_addsub_pure_helper hp ctx (cfg := {}) rfl (by decide) legacy
theorem stock_addsub_extend_helper {p : Program} (hp : Data p) (ctx : Ctx) (subtract : Bool)
    {w z : Nat} (width : w ≤ 64) {rz : Reg} (mapped : ctx.valueReg? z = some rz)
    (st : State) (safe : DemandAllowed ctx st z) (tr : Array RuleId) (n : Nat) (rx : Reg) (e : ExtendOp) :
    (applyTerm p (Stock.sem ctx) {} (n+50) 27 (if subtract then 439 else 434)
      [.ty (.int w),.reg rx,.op (.extended z e)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark z with base := (st.base.fresh .int).2.emit (.aluRRRExtend (if subtract then .sub else .add)
          (szOf w) (st.base.fresh .int).1 rx rz e)},
        (((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2684.id).push rule_inst_2693.id).push
          (if subtract then rule_inst_3146.id else rule_inst_3126.id)) := by
  have request := stock_put_extended_in_reg ctx st z e rz mapped safe
  have ext : ∀ q,Stock.externCtor ctx T.get_extended_op [.op (.extended z e)] q = .ok (.data 84 e.idx [],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.get_extended_op _ q (by decide)]; rfl
  have helper := fun q trace fuel => stock_addsub_extend_reg hp ctx subtract width q trace fuel rx rz e
  cases hp
  cases subtract
  all_goals simp only [Bool.false_eq_true,ite_true,ite_false] at *
  all_goals isel_eval [*,rule_inst_3126,rule_inst_3146,rule_inst_2693,sem_ctor,sem_mkData]
  all_goals rfl
def extendRule (subtract left : Bool) : Rule :=
  if subtract then rule_lower_816 else if left then rule_lower_111 else rule_lower_108
def extendEnv (left : Bool) (w x z : Nat) (e : ExtendOp) : Isle.Interp.Env V :=
  if left then env3 (.ty (.int w)) (.op (.extended z e)) (.value x)
  else env3 (.ty (.int w)) (.value x) (.op (.extended z e))
theorem stock_addsub_extend_rhs {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x z : Nat} (width : w ≤ 64) (e : ExtendOp)
    {rx rz : Reg} (mapX : ctx.valueReg? x = some rx) (mapZ : ctx.valueReg? z = some rz)
    (st : State) (safeX : DemandAllowed ctx st x) (safeZ : DemandAllowed ctx st z) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+70) (extendRule subtract left).rhs
      (extendEnv left w x z e)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark z with base := ((st.base.fresh .int).2.emit
          (.aluRRRExtend (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx rz e))},trace) := by
  have request := stock_put_in_reg ctx st x rx mapX safeX
  have helper := fun trace fuel => stock_addsub_extend_helper hp ctx subtract width mapZ (st.mark x) safeZ trace fuel rx e
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases subtract <;> cases left
  · refine Exists.intro ?traceAddRight ?proofAddRight
    case proofAddRight =>
      simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_108,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceAddLeft ?proofAddLeft
    case proofAddLeft =>
      simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_111,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceSub ?proofSub
    case proofSub =>
      simp only [extendRule,extendEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_816,sem_ctor,sem_mkData]
      all_goals rfl
  · cases side rfl
def immRule (subtract left : Bool) : Rule :=
  if subtract then rule_lower_805 else if left then rule_lower_93 else rule_lower_90
def immEnv (left : Bool) (w x : Nat) (imm : Imm12) : Isle.Interp.Env V :=
  if left then env3 (.ty (.int w)) (.op (.imm12 imm)) (.value x)
  else env3 (.ty (.int w)) (.value x) (.op (.imm12 imm))
theorem stock_addsub_imm_rhs {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x : Nat} (width : w ≤ 64) (imm : Imm12)
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) (immRule subtract left).rhs
      (immEnv left w x imm)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := ((st.base.fresh .int).2.emit
          (.aluRRImm12 (if subtract then .sub else .add) (szOf w) (st.base.fresh .int).1 rx imm))},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have helper := fun q trace fuel => stock_addsub_imm_helper hp ctx subtract width q trace fuel rx imm
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases subtract <;> cases left
  · refine Exists.intro ?traceAddRight ?proofAddRight
    case proofAddRight =>
      simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_90,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceAddLeft ?proofAddLeft
    case proofAddLeft =>
      simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_93,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceSub ?proofSub
    case proofSub =>
      simp only [immRule,immEnv,Bool.false_eq_true,ite_true,ite_false] at *
      isel_eval [*,rule_lower_805,sem_ctor,sem_mkData]
      all_goals rfl
  · cases side rfl
def negImmRule (subtract left : Bool) : Rule :=
  if subtract then rule_lower_810 else if left then rule_lower_102 else rule_lower_98
def negImmEnv (left : Bool) (w x y : Nat) (imm : Imm12) : Isle.Interp.Env V :=
  if left then env4 (.ty (.int w)) (.value y) (.value x) (.op (.imm12 imm))
  else env4 (.ty (.int w)) (.value x) (.value y) (.op (.imm12 imm))
theorem stock_addsub_neg_imm_rhs {p : Program} (hp : Data p) (ctx : Ctx) (subtract left : Bool)
    (side : subtract = true → left = false) {w x y : Nat} (width : w ≤ 64) (imm : Imm12)
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) (negImmRule subtract left).rhs
      (negImmEnv left w x y imm)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := ((st.base.fresh .int).2.emit
          (.aluRRImm12 (if subtract then .add else .sub) (szOf w) (st.base.fresh .int).1 rx imm))},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have helper := fun q trace fuel => stock_addsub_imm_helper hp ctx (!subtract) width q trace fuel rx imm
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases subtract <;> cases left
  · refine Exists.intro ?traceAddRight ?proofAddRight
    case proofAddRight =>
      simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false,Bool.not_false,Bool.not_true] at *
      isel_eval [*,rule_lower_98,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceAddLeft ?proofAddLeft
    case proofAddLeft =>
      simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false,Bool.not_false,Bool.not_true] at *
      isel_eval [*,rule_lower_102,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceSub ?proofSub
    case proofSub =>
      simp only [negImmRule,negImmEnv,Bool.false_eq_true,ite_true,ite_false,Bool.not_false,Bool.not_true] at *
      isel_eval [*,rule_lower_810,sem_ctor,sem_mkData]
      all_goals rfl
  · cases side rfl
end Backend.Stock.Proof.ScalarAddSub

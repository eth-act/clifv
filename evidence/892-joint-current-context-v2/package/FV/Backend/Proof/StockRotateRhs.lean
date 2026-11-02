import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockShiftHelper
import FV.Backend.Proof.StockRotateSemantics
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_zero (ctx : Ctx) : (Stock.sem ctx).int 6 0 = .int 0 := rfl
end Numbers
private theorem get_reg (ctx : Ctx) (st : State) (r : Reg) :
    Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] st = .ok (.reg r,st) := by
  rw [stock_ctor_baseOnly ctx T.value_regs_get _ st (by decide)]; rfl
private theorem zero_reg (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]; rfl
/-- Wide right-rotate helper emits the real register EXTR and preserves all
Stock scheduling fields. -/
theorem stock_rotate_rr_helper {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat}
    (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 513 [.ty (.int w),.reg rx,.reg ry]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR .extr (szOf w) (st.base.fresh .int).1 rx ry)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3478.id) := by
  have inner := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl width (k := 15) (op := .extr) rfl q trace fuel rx ry
  cases hp
  isel_eval [*,rule_inst_3478,sem_mkData]
/-- Actual immediate EXTR helper does not request the looked-through amount. -/
theorem stock_rotate_imm_helper {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat}
    (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (amount : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 514 [.ty (.int w),.reg rx,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmShift .extr (szOf w) (st.base.fresh .int).1 rx amount)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2537.id).push rule_inst_3482.id) := by
  have inner := fun q trace fuel => ScalarShift.stock_shift_imm_helper hp ctx (cfg := {}) rfl width (k := 15) (op := .extr) rfl q trace fuel rx amount
  cases hp
  isel_eval [*,rule_inst_3482,sem_mkData]
private theorem sub_run {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat}
    (width : w ≤ 64) (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 437 [.ty (.int w),.reg rx,.reg ry]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 rx ry)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3138.id) := by
  have inner := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl width (k := 1) (op := .sub) rfl q trace fuel rx ry
  cases hp
  isel_eval [*,rule_inst_3138,sem_mkData]
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
def rotateWidth (wide : Bool) : Nat := if wide then 64 else 32
def rotateWideRule (left wide : Bool) : Rule :=
  if left then (if wide then rule_lower_1797 else rule_lower_1791)
  else (if wide then rule_lower_1848 else rule_lower_1844)
def rotateWideEnv (left : Bool) (x y : Nat) : Isle.Interp.Env V :=
  if left then ((Array.replicate 4 none).setIfInBounds 0 (some (.value x))).setIfInBounds 1 (some (.value y))
  else env2 (.value x) (.value y)
def rotateWideBase (left wide : Bool) (st : LState) (rx ry : Reg) : LState :=
  if left then
    (((st.fresh .int).2.emit (.aluRRR .sub (szOf (rotateWidth wide)) (st.fresh .int).1 .xzr ry)).fresh .int).2.emit
      (.aluRRR .extr (szOf (rotateWidth wide)) (.vreg (st.nextVreg+1) .int) rx (st.fresh .int).1)
  else (st.fresh .int).2.emit (.aluRRR .extr (szOf (rotateWidth wide)) (st.fresh .int).1 rx ry)
def rotateWideRequests (left : Bool) (st : State) (x y : Nat) : State :=
  if left then (st.mark y).mark x else (st.mark x).mark y
/-- All four register-count wide roots derive the actual marked state and
complete one/two-instruction fragment from guarded mapped requests. -/
theorem stock_rotate_wide_rhs {p : Program} (hp : Data p) (ctx : Ctx) (left wide : Bool)
    {x y : Nat} {rx ry : Reg} (mappedX : ctx.valueReg? x = some rx) (mappedY : ctx.valueReg? y = some ry)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+60) (rotateWideRule left wide).rhs (rotateWideEnv left x y)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (rotateWideResult left st.base.nextVreg) .int]]),
        {rotateWideRequests left st x y with base := rotateWideBase left wide st.base rx ry},trace) := by
  have width : rotateWidth wide ≤ 64 := by cases wide <;> decide
  have requestX := stock_put_in_reg ctx st x rx mappedX safeX
  have requestYX := stock_put_in_reg ctx (st.mark y) x rx mappedX safeX
  have requestAfterNeg := stock_put_in_reg ctx
    {st.mark y with base := (((st.mark y).base.fresh .int).2.emit
      (.aluRRR .sub (szOf (rotateWidth wide)) ((st.mark y).base.fresh .int).1 .xzr ry))} x rx mappedX safeX
  have requestY := stock_put_in_regs ctx st y ry mappedY safeY
  have requestXY := stock_put_in_regs ctx (st.mark x) y ry mappedY safeY
  have get := fun q => get_reg ctx q ry
  have zero := fun q => zero_reg ctx q
  have sub := fun q trace fuel => sub_run hp ctx width q trace fuel .xzr ry
  have rot := fun q trace fuel a b => stock_rotate_rr_helper hp ctx width q trace fuel a b
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases left <;> cases wide
  · refine Exists.intro ?traceRight32 ?proofRight32
    case proofRight32 =>
      simp only [rotateWideRule,rotateWideEnv,rotateWideBase,rotateWideRequests,rotateWideResult,
        rotateWidth,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1791,rule_lower_1797,rule_lower_1844,rule_lower_1848,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceRight64 ?proofRight64
    case proofRight64 =>
      simp only [rotateWideRule,rotateWideEnv,rotateWideBase,rotateWideRequests,rotateWideResult,
        rotateWidth,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1791,rule_lower_1797,rule_lower_1844,rule_lower_1848,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceLeft32 ?proofLeft32
    case proofLeft32 =>
      simp only [rotateWideRule,rotateWideEnv,rotateWideBase,rotateWideRequests,rotateWideResult,
        rotateWidth,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1791,rule_lower_1797,rule_lower_1844,rule_lower_1848,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceLeft64 ?proofLeft64
    case proofLeft64 =>
      simp only [rotateWideRule,rotateWideEnv,rotateWideBase,rotateWideRequests,rotateWideResult,
        rotateWidth,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1791,rule_lower_1797,rule_lower_1844,rule_lower_1848,sem_ctor,sem_prim,sem_zero]
      rfl
private theorem negate_count (ctx : Ctx) (st : State) {w n : Nat}
    (width : IW w) (count : n < w) :
    Stock.externCtor ctx T.negate_imm_shift [.ty (.int w),.op (.immShift n)] st =
      .ok (.op (.immShift ((w-n)%w)),st) := by
  rw [stock_ctor_baseOnly ctx T.negate_imm_shift _ st (by decide)]
  change (.ok (.op (.immShift (Nat.land ((w+256-n)%256) (w-1))),st) : ExtResult (V × State)) = _
  rw [neg_imm width count]
def rotateWideImmRule (left wide : Bool) : Rule :=
  if left then (if wide then rule_lower_1808 else rule_lower_1803)
  else (if wide then rule_lower_1862 else rule_lower_1857)
/-- All four wide immediate roots request only the original data operand;
the actual normalized/negated count emits one EXTR and leaves the count's
looked-through source register unmaterialized. -/
theorem stock_rotate_wide_imm_rhs {p : Program} (hp : Data p) (ctx : Ctx) (left wide : Bool)
    {x : Nat} {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    {amount : Nat} (count : amount < rotateWidth wide) (constant : Int)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) (rotateWideImmRule left wide).rhs
      (env3 (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := ((st.base.fresh .int).2.emit
          (.aluRRImmShift .extr (szOf (rotateWidth wide)) (st.base.fresh .int).1 rx
            (rotateImmediate left (rotateWidth wide) amount)))},trace) := by
  have width : rotateWidth wide ≤ 64 := by cases wide <;> decide
  have iw : IW (rotateWidth wide) := by cases wide <;> simp [rotateWidth,IW]
  have request := stock_put_in_reg ctx st x rx mapped safe
  have negate := fun q => negate_count ctx q iw count
  have helper := fun q trace fuel a => stock_rotate_imm_helper hp ctx width q trace fuel rx a
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases left <;> cases wide
  · refine Exists.intro ?traceImmRight32 ?proofImmRight32
    case proofImmRight32 =>
      simp only [rotateWideImmRule,rotateWidth,rotateImmediate,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1803,rule_lower_1808,rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      rfl
  · refine Exists.intro ?traceImmRight64 ?proofImmRight64
    case proofImmRight64 =>
      simp only [rotateWideImmRule,rotateWidth,rotateImmediate,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1803,rule_lower_1808,rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      rfl
  · refine Exists.intro ?traceImmLeft32 ?proofImmLeft32
    case proofImmLeft32 =>
      simp only [rotateWideImmRule,rotateWidth,rotateImmediate,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1803,rule_lower_1808,rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      rfl
  · refine Exists.intro ?traceImmLeft64 ?proofImmLeft64
    case proofImmLeft64 =>
      simp only [rotateWideImmRule,rotateWidth,rotateImmediate,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1803,rule_lower_1808,rule_lower_1857,rule_lower_1862,sem_ctor,sem_prim]
      rfl
end Backend.Stock.Proof.ScalarRotate

import FV.Backend.Proof.StockRotateRhs
import FV.Backend.Proof.StockRotateNarrowRhs
namespace Backend.Stock.Proof.ScalarRotate
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_int32 (ctx : Ctx) : (Stock.sem ctx).int 1 32 = .int 32 := rfl
end Numbers
private theorem ty_bits (ctx : Ctx) (st : State) (t : CTy) :
    Stock.externCtor ctx T.ty_bits [.ty t] st = .ok (.int t.bits,st) := by
  rw [stock_ctor_baseOnly ctx T.ty_bits _ st (by decide)]; rfl
private theorem zext32_run {p : Program} (hp : Data p) (ctx : Ctx) {x : Nat} {rx : Reg} {t : CTy}
    (mapped : ctx.valueReg? x = some rx) (typed : ctx.valueType? x = some t)
    (not32 : t ≠ .int 32) (not64 : t ≠ .int 64) (small : t.bits ≤ 32)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+40) 27 556 [.value x]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx false t.bits 32)},
        (tr.push rule_inst_2991.id).push rule_inst_3809.id) := by
  have getTy := ext_value_type ctx st.base typed
  have n32 : (V.ty t == V.ty (.int 32)) = false := by simp [not32]
  have n64 : (V.ty t == V.ty (.int 64)) = false := by simp [not64]
  have fits := ext_fits_in_32_ty ctx st.base t
  simp only [small,ite_true] at fits
  have bits := fun q t => ty_bits ctx q t
  have request := stock_put_in_reg ctx st x rx mapped safe
  have ext := fun q trace fuel a => ScalarShift.stock_extend_helper hp ctx (cfg := {}) rfl q trace fuel a false t.bits 32
  have temp : ∀ q : State,Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] q =
      .ok (.reg (q.base.fresh .int).1,{q with base := (q.base.fresh .int).2}) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.temp_writable_reg _ q (by decide)]
    rfl
  have writable : ∀ (q : State) (r : Reg),Stock.externCtor ctx T.writable_reg_to_reg [.reg r] q = .ok (.reg r,q) := by
    intro q r
    rw [stock_ctor_baseOnly ctx T.writable_reg_to_reg _ q (by decide)]
    rfl
  have emitted : ∀ (q : State) (rd rn : Reg),Stock.externCtor ctx T.emit
      [.data 58 28 [.reg rd,.reg rn,.bool false,.int t.bits,.int 32]] q =
      .ok (.op .unit,{q with base := q.base.emit (.extend rd rn false t.bits 32)}) := by
    intro q rd rn
    rw [stock_ctor_baseOnly ctx T.emit _ q (by decide)]
    have baseEmit := ctor_emit ctx q.base (ofV_extend_fb rd rn false t.bits 32)
    change Backend.externCtor ctx T.emit [.data 58 28 [.reg rd,.reg rn,.bool false,.int t.bits,.int 32]] q.base =
      .ok (.op .unit,q.base.emit (.extend rd rn false t.bits 32)) at baseEmit
    rw [baseEmit]
  cases hp
  isel_eval [*,rule_inst_3809,rule_inst_3813,rule_inst_3814,rule_inst_2991,sem_ctor,sem_extract,sem_unData,sem_eq,sem_mkData,sem_prim,sem_bool,sem_int32]
  rfl
/-- Narrow rotation's actual preparation marks the guarded mapped source
and zero-extends its original typed low bits into a fresh physical32 register.
The selected-source proof derives the type from original frame consistency. -/
theorem stock_rotate_zext32 {p : Program} (hp : Data p) (ctx : Ctx) {w x : Nat}
    (width : w = 8 ∨ w = 16) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (typed : ctx.valueType? x = some (.int w)) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+40) 27 556 [.value x]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx false w 32)},
        (tr.push rule_inst_2991.id).push rule_inst_3809.id) := by
  simpa only [CTy.bits] using zext32_run hp ctx mapped typed
    (by rcases width with rfl | rfl <;> decide) (by rcases width with rfl | rfl <;> decide)
    (by change w ≤ 32; rcases width with h | h <;> omega) st safe tr n
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
private theorem get_reg (ctx : Ctx) (st : State) (r : Reg) :
    Stock.externCtor ctx T.value_regs_get [.regs [r],.int 0] st = .ok (.reg r,st) := by
  rw [stock_ctor_baseOnly ctx T.value_regs_get _ st (by decide)]; rfl
private theorem zero_reg (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]; rfl
private theorem negate_count (ctx : Ctx) (st : State) {w n : Nat}
    (width : IW w) (count : n < w) :
    Stock.externCtor ctx T.negate_imm_shift [.ty (.int w),.op (.immShift n)] st =
      .ok (.op (.immShift ((w-n)%w)),st) := by
  rw [stock_ctor_baseOnly ctx T.negate_imm_shift _ st (by decide)]
  change (.ok (.op (.immShift (Nat.land ((w+256-n)%256) (w-1))),st) : ExtResult (V × State)) = _
  rw [neg_imm width count]
section Zero
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_zero (ctx : Ctx) : (Stock.sem ctx).int 6 0 = .int 0 := rfl
end Zero
def rotateNarrowRule (left immediate : Bool) : Rule :=
  if immediate then (if left then rule_lower_1778 else rule_lower_1852)
  else (if left then rule_lower_1772 else rule_lower_1840)
def rotateNarrowEnv (left : Bool) (w x y : Nat) : Isle.Interp.Env V :=
  if left then (((Array.replicate 5 none).setIfInBounds 0 (some (.ty (.int w)))).setIfInBounds 1
    (some (.value x))).setIfInBounds 2 (some (.value y))
  else env3 (.ty (.int w)) (.value x) (.value y)
def rotateNarrowStart (left : Bool) (st : LState) (ry : Reg) : LState :=
  if left then (st.fresh .int).2.emit (.aluRRR .sub .size32 (st.fresh .int).1 .xzr ry) else st
def rotateNarrowRootBase (left : Bool) (w : Nat) (st : LState) (rx ry : Reg) : LState :=
  let start := rotateNarrowStart left st ry
  let ext := (start.fresh .int).2.emit (.extend (start.fresh .int).1 rx false w 32)
  rotateNarrowRegBase w ext (start.fresh .int).1 (if left then (st.fresh .int).1 else ry)
def rotateNarrowRootResult (left : Bool) (d : Nat) : Nat := if left then d+7 else d+6
/-- Actual narrow register roots account for count negation, original typed
zero-extension, both guarded mapped requests and all six helper instructions.
Input typing is an internal premise derived from source-frame consistency when
this execution contract is composed with successful selection. -/
theorem stock_rotate_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {w x y : Nat} (width : w = 8 ∨ w = 16) {rx ry : Reg}
    (mappedX : ctx.valueReg? x = some rx) (mappedY : ctx.valueReg? y = some ry)
    (typed : ctx.valueType? x = some (.int w)) (st : State)
    (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+160) (rotateNarrowRule left false).rhs
      (rotateNarrowEnv left w x y)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (rotateNarrowRootResult left st.base.nextVreg) .int]]),
        {rotateWideRequests left st x y with base := rotateNarrowRootBase left w st.base rx ry},trace) := by
  have requestY := stock_put_in_regs ctx st y ry mappedY safeY
  have get := fun q => get_reg ctx q ry
  have zero := fun q => zero_reg ctx q
  have sub := fun q trace fuel => sub_run hp ctx (w := 32) (by decide) q trace fuel .xzr ry
  have helper := fun q trace fuel a b => stock_rotate_narrow_rr_run hp ctx width q trace fuel a b
  have zext := fun trace fuel => stock_rotate_zext32 hp ctx width mappedX typed st safeX trace fuel
  let neg := {st.mark y with base := (((st.mark y).base.fresh .int).2.emit
    (.aluRRR .sub (szOf 32) ((st.mark y).base.fresh .int).1 .xzr ry))}
  have zextAfterNeg := fun trace fuel => stock_rotate_zext32 hp ctx width mappedX typed neg safeX trace fuel
  have requestAfterExt := stock_put_in_regs ctx
    {st.mark x with base := ((st.base.fresh .int).2.emit
      (.extend (st.base.fresh .int).1 rx false w 32))} y ry mappedY safeY
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases left <;> rcases width with rfl | rfl
  · refine Exists.intro ?traceRight8 ?proofRight8
    case proofRight8 =>
      simp only [rotateNarrowRule,rotateNarrowEnv,rotateNarrowRootBase,rotateNarrowStart,
        rotateNarrowRootResult,rotateWideRequests,neg,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1772,rule_lower_1840,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceRight16 ?proofRight16
    case proofRight16 =>
      simp only [rotateNarrowRule,rotateNarrowEnv,rotateNarrowRootBase,rotateNarrowStart,
        rotateNarrowRootResult,rotateWideRequests,neg,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1772,rule_lower_1840,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceLeft8 ?proofLeft8
    case proofLeft8 =>
      simp only [rotateNarrowRule,rotateNarrowEnv,rotateNarrowRootBase,rotateNarrowStart,
        rotateNarrowRootResult,rotateWideRequests,neg,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1772,rule_lower_1840,sem_ctor,sem_prim,sem_zero]
      rfl
  · refine Exists.intro ?traceLeft16 ?proofLeft16
    case proofLeft16 =>
      simp only [rotateNarrowRule,rotateNarrowEnv,rotateNarrowRootBase,rotateNarrowStart,
        rotateNarrowRootResult,rotateWideRequests,neg,Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1772,rule_lower_1840,sem_ctor,sem_prim,sem_zero]
      rfl
def rotateNarrowImmRootBase (left : Bool) (w : Nat) (st : LState) (rx : Reg) (amount : Nat) : LState :=
  let ext := (st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false w 32)
  rotateNarrowImmBase w ext (st.fresh .int).1 (rotateImmediate left w amount)
/-- Both narrow immediate roots request and zero-extend only the original data
operand, then emit the actual three-instruction helper at the normalized count.
The selected-source composition derives typing and constant/count facts. -/
theorem stock_rotate_narrow_imm_rhs {p : Program} (hp : Data p) (ctx : Ctx) (left : Bool)
    {w x amount : Nat} (width : w = 8 ∨ w = 16) (count : amount < w) (constant : Int)
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (typed : ctx.valueType? x = some (.int w))
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+140) (rotateNarrowRule left true).rhs
      (env4 (.ty (.int w)) (.value x) (.int constant) (.op (.immShift amount)))).run (st,tr) =
      .ok (some (.regsVec [[.vreg (st.base.nextVreg+3) .int]]),
        {st.mark x with base := rotateNarrowImmRootBase left w st.base rx amount},trace) := by
  have iw : IW w := by rcases width with rfl | rfl <;> simp [IW]
  have fits : rotateImmediate left w amount < w := by
    cases left
    · exact count
    · exact Nat.mod_lt _ iw.pos
  have ext := fun trace fuel => stock_rotate_zext32 hp ctx width mapped typed st safe trace fuel
  have negate := fun q => negate_count ctx q iw count
  have helper := fun q trace fuel r => stock_rotate_narrow_imm_run hp ctx width fits q trace fuel r
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases left <;> rcases width with rfl | rfl
  · refine Exists.intro ?traceImmRight8 ?proofImmRight8
    case proofImmRight8 =>
      simp only [rotateNarrowRule,rotateNarrowImmRootBase,rotateImmediate,
        Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1778,rule_lower_1852,sem_ctor]
      rfl
  · refine Exists.intro ?traceImmRight16 ?proofImmRight16
    case proofImmRight16 =>
      simp only [rotateNarrowRule,rotateNarrowImmRootBase,rotateImmediate,
        Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1778,rule_lower_1852,sem_ctor]
      rfl
  · refine Exists.intro ?traceImmLeft8 ?proofImmLeft8
    case proofImmLeft8 =>
      simp only [rotateNarrowRule,rotateNarrowImmRootBase,rotateImmediate,
        Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1778,rule_lower_1852,sem_ctor]
      rfl
  · refine Exists.intro ?traceImmLeft16 ?proofImmLeft16
    case proofImmLeft16 =>
      simp only [rotateNarrowRule,rotateNarrowImmRootBase,rotateImmediate,
        Bool.false_eq_true,ite_false,ite_true] at *
      isel_eval [*,rule_lower_1778,rule_lower_1852,sem_ctor]
      rfl
end Backend.Stock.Proof.ScalarRotate

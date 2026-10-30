import FV.Backend.Proof.IselFamAluBShiftTerms
import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockLogicalForms
import FV.Backend.Proof.StockShiftHelper
import FV.Backend.Proof.StockBitHelper
import FV.Backend.Proof.StockImm12Helper
namespace Backend.Stock.Proof.ScalarCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_mkData (ctx : Ctx) (t k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData t k vs = .data t k vs := rfl
private theorem output_run {p : Program} (hp : Data p) (ctx : Ctx) (st : State) (tr : Array RuleId)
    (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+10) 25 172 [.reg r]).run (st,tr) =
      .ok (some (.regsVec [[r]]),st,tr.push rule_prelude_lower_105.id) := by
  have value : ∀ q,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have output : ∀ q,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,sem_ctor]
private theorem rbit_run {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (small : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 517 [.ty (.int w),.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.base.fresh .int).1 r)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2733.id).push rule_inst_3512.id) := by
  have inner := fun q trace fuel => ScalarBit.stock_bit_rr_helper hp ctx (cfg := {}) rfl small (k := 0) (op := .rbit) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3512,sem_mkData]
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem clz_run {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (small : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 518 [.ty (.int w),.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitRR .clz (szOf w) (st.base.fresh .int).1 r)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2733.id).push rule_inst_3517.id) := by
  have inner := fun q trace fuel => ScalarBit.stock_bit_rr_helper hp ctx (cfg := {}) rfl small (k := 1) (op := .clz) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3517,sem_mkData]
def countRule (trailing : Bool) (w : Nat) : Rule :=
  if trailing then (if w = 8 then rule_lower_1982 else if w = 16 then rule_lower_1986 else rule_lower_1995)
  else (if w = 8 then rule_lower_1951 else if w = 16 then rule_lower_1955 else rule_lower_1961)
def countOpcode (trailing : Bool) : Nat := if trailing then 109 else 107
def countOp (trailing : Bool) : Clif.UnaryOp := if trailing then .ctz else .clz
def countEnv (w x : Nat) : Isle.Interp.Env V :=
  if w = 8 ∨ w = 16 then env1 (.value x) else env2 (.ty (.int w)) (.value x)
section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_int16 (ctx : Ctx) : (Stock.sem ctx).int 1 16 = .int 16 := rfl
private theorem sem_int24 (ctx : Ctx) : (Stock.sem ctx).int 1 24 = .int 24 := rfl
private theorem sem_int32 (ctx : Ctx) : (Stock.sem ctx).int 1 32 = .int 32 := rfl
end Numbers
/-- All six actual count matches preserve complete scheduling state/trace and
bind the original source operand with the root's canonical environment. -/
theorem stock_count_match {p : Program} (hp : Data p) (ctx : Ctx) (trailing : Bool)
    {i x w : Nat} {info : IInfo} (width : IW w) (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 (countOpcode trailing) [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (countRule trailing w) [.inst i]).run (st,tr) =
      .ok (some (countEnv w x),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  cases trailing <;> rcases width with rfl | rfl | rfl | rfl
  all_goals simp only [countRule,countOpcode,countEnv,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,false_or,or_false,true_or,or_true] at extraction ⊢
  all_goals isel_eval [*,countRule,countOpcode,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
    rule_lower_1982,rule_lower_1986,rule_lower_1995,sem_extract,sem_unData,sem_prim,sem_eq]
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
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
private theorem sub_imm_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) (imm : Imm12) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 438 [.ty (.int 32),.reg r,.op (.imm12 imm)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImm12 .sub .size32 (st.base.fresh .int).1 r imm)},
        ((tr.push rule_inst_1592.id).push rule_inst_2648.id).push rule_inst_3142.id) := by
  have inner := fun q trace fuel => stock_alu_imm12_helper hp ctx (cfg := {}) rfl (w := 32) (k := 1) (op := .sub) (by decide) rfl q trace fuel r imm
  cases hp
  isel_eval [*,rule_inst_3142,sem_mkData]
  rfl
private theorem orr_imm_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) (imm : ImmLogic) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 498 [.ty (.int 32),.reg r,.op (.immLogic imm)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmLogic .orr .size32 (st.base.fresh .int).1 r imm)},
        ((tr.push rule_inst_1592.id).push rule_inst_2529.id).push rule_inst_3416.id) := by
  have inner := fun q trace fuel => LogicalForms.stock_logical_imm_helper hp ctx (cfg := {}) rfl (w := 32) (k := 2) (op := .orr) (by decide) rfl q trace fuel r imm
  cases hp
  isel_eval [*,rule_inst_3416,sem_mkData]
  rfl
section Numbers2
attribute [local semireducible] Isle.Aarch64.program
private theorem sem_mask8 (ctx : Ctx) : (Stock.sem ctx).int 4 8388608 = .int 8388608 := rfl
private theorem sem_mask16 (ctx : Ctx) : (Stock.sem ctx).int 4 32768 = .int 32768 := rfl
end Numbers2
private theorem imm12_16 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.u8_into_imm12 [.int 16] st = .ok (.op (.imm12 ⟨16,false⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.u8_into_imm12 _ st (by decide)]; rfl
private theorem imm12_24 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.u8_into_imm12 [.int 24] st = .ok (.op (.imm12 ⟨24,false⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.u8_into_imm12 _ st (by decide)]; rfl
private theorem mask8 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.u64_into_imm_logic [.ty (.int 32),.int 8388608] st = .ok (.op (.immLogic ⟨8388608,.size32⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.u64_into_imm_logic _ st (by decide)]; rfl
private theorem mask16 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.u64_into_imm_logic [.ty (.int 32),.int 32768] st = .ok (.op (.immLogic ⟨32768,.size32⟩),st) := by
  rw [stock_ctor_baseOnly ctx T.u64_into_imm_logic _ st (by decide)]; rfl

def countWideBase (trailing : Bool) (w : Nat) (st : LState) (rx : Reg) : LState :=
  if trailing then (((st.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.fresh .int).1 rx)).fresh .int).2.emit
    (.bitRR .clz (szOf w) (.vreg (st.nextVreg+1) .int) (st.fresh .int).1)
  else (st.fresh .int).2.emit (.bitRR .clz (szOf w) (st.fresh .int).1 rx)
def countNarrowBase (trailing : Bool) (w : Nat) (st : LState) (rx : Reg) : LState :=
  if trailing then
    (((((st.fresh .int).2.emit (.bitRR .rbit .size32 (st.fresh .int).1 rx)).fresh .int).2.emit
      (.aluRRImmLogic .orr .size32 (.vreg (st.nextVreg+1) .int) (st.fresh .int).1 ⟨2^(32-w-1),.size32⟩)).fresh .int).2.emit
      (.bitRR .clz .size32 (.vreg (st.nextVreg+2) .int) (.vreg (st.nextVreg+1) .int))
  else
    (((((st.fresh .int).2.emit (.extend (st.fresh .int).1 rx false w 32)).fresh .int).2.emit
      (.bitRR .clz .size32 (.vreg (st.nextVreg+1) .int) (st.fresh .int).1)).fresh .int).2.emit
      (.aluRRImm12 .sub .size32 (.vreg (st.nextVreg+2) .int) (.vreg (st.nextVreg+1) .int) ⟨32-w,false⟩)
/-- Actual32/64-bit count RHSs mark the source once and emit their complete
one/two-instruction fragments, preserving every other scheduling field. -/
theorem stock_count_wide_rhs {p : Program} (hp : Data p) (ctx : Ctx) (trailing : Bool)
    {x w : Nat} (width : w = 32 ∨ w = 64) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (countRule trailing w).rhs (countEnv w x)).run (st,tr) =
      .ok (some (.regsVec [[.vreg (st.base.nextVreg+(if trailing then 1 else 0)) .int]]),
        {st.mark x with base := countWideBase trailing w st.base rx},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have clz := fun q trace fuel r => clz_run hp ctx (w := w) (by rcases width with rfl | rfl <;> decide) q trace fuel r
  have rbit := fun q trace fuel r => rbit_run hp ctx (w := w) (by rcases width with rfl | rfl <;> decide) q trace fuel r
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  cases trailing <;> rcases width with rfl | rfl
  · refine Exists.intro ?trace_lz32 ?proof_lz32
    case proof_lz32 =>
      simp only [countRule,countEnv,countWideBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,false_or,Nat.add_zero]
      isel_eval [*,rule_lower_1961,sem_ctor]
      rfl
  · refine Exists.intro ?trace_lz64 ?proof_lz64
    case proof_lz64 =>
      simp only [countRule,countEnv,countWideBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,false_or,Nat.add_zero]
      isel_eval [*,rule_lower_1961,sem_ctor]
      rfl
  · refine Exists.intro ?trace_tz32 ?proof_tz32
    case proof_tz32 =>
      simp only [countRule,countEnv,countWideBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,false_or,Nat.add_zero]
      isel_eval [*,rule_lower_1995,sem_ctor]
      rfl
  · refine Exists.intro ?trace_tz64 ?proof_tz64
    case proof_tz64 =>
      simp only [countRule,countEnv,countWideBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff,false_or,Nat.add_zero]
      isel_eval [*,rule_lower_1995,sem_ctor]
      rfl
/-- The real narrow CLZ RHS emits extension, count and width correction
through its actual typed request; all scheduling fields are retained. -/
theorem stock_clz_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w = 8 ∨ w = 16) (typed : ctx.valueType? x = some (.int w))
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) =
      .ok (some (.regsVec [[.vreg (st.base.nextVreg+2) .int]]),
        {st.mark x with base := countNarrowBase false w st.base rx},trace) := by
  have zext := fun trace fuel => zext32_run hp ctx mapped typed
    (by rcases width with rfl | rfl <;> decide) (by rcases width with rfl | rfl <;> decide)
    (by rcases width with rfl | rfl <;> decide) st safe trace fuel
  have clz := fun q trace fuel r => clz_run hp ctx (w := 32) (by decide) q trace fuel r
  have sub := fun q trace fuel r imm => sub_imm_run hp ctx q trace fuel r imm
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have imm16 := fun q => imm12_16 ctx q
  have imm24 := fun q => imm12_24 ctx q
  cases hp
  rcases width with rfl | rfl
  · refine Exists.intro ?trace_lz8 ?proof_lz8
    case proof_lz8 =>
      simp only [countRule,countNarrowBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff]
      isel_eval [*,rule_lower_1951,sem_ctor,sem_prim,sem_int16,sem_int24]
      rfl
  · refine Exists.intro ?trace_lz16 ?proof_lz16
    case proof_lz16 =>
      simp only [countRule,countNarrowBase,Bool.false_eq_true,ite_false,ite_true,Nat.reduceEqDiff]
      isel_eval [*,rule_lower_1955,sem_ctor,sem_prim,sem_int16,sem_int24]
      rfl
/-- The real narrow CTZ RHS emits reversal, sentinel OR and leading count;
upper source bits cannot change the final narrow count. -/
theorem stock_ctz_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w = 8 ∨ w = 16) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (countRule true w).rhs (env1 (.value x))).run (st,tr) =
      .ok (some (.regsVec [[.vreg (st.base.nextVreg+2) .int]]),
        {st.mark x with base := countNarrowBase true w st.base rx},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have clz := fun q trace fuel r => clz_run hp ctx (w := 32) (by decide) q trace fuel r
  have rbit := fun q trace fuel r => rbit_run hp ctx (w := 32) (by decide) q trace fuel r
  have orr := fun q trace fuel r imm => orr_imm_run hp ctx q trace fuel r imm
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have imm8 := fun q => mask8 ctx q
  have imm16 := fun q => mask16 ctx q
  cases hp
  rcases width with rfl | rfl
  · refine Exists.intro ?trace_tz8 ?proof_tz8
    case proof_tz8 =>
      simp only [countRule,countNarrowBase,ite_true,ite_false,Nat.reduceEqDiff]
      isel_eval [*,rule_lower_1982,sem_ctor,sem_prim,sem_mask8,sem_mask16]
      rfl
  · refine Exists.intro ?trace_tz16 ?proof_tz16
    case proof_tz16 =>
      simp only [countRule,countNarrowBase,ite_true,ite_false,Nat.reduceEqDiff]
      isel_eval [*,rule_lower_1986,sem_ctor,sem_prim,sem_mask8,sem_mask16]
      rfl
/-- Actual successful wide execution derives its guarded mapped source request. -/
theorem stock_count_wide_requests {p : Program} (hp : Data p) (ctx : Ctx) (trailing : Bool)
    {w x n : Nat} (width : w = 32 ∨ w = 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule trailing w).rhs (countEnv w x)).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule trailing w).rhs (countEnv w x)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases trailing <;> rcases width with rfl | rfl
      all_goals simp only [countRule,countEnv,Bool.false_eq_true,ite_false,ite_true,
        Nat.reduceEqDiff,false_or,or_false,true_or,or_true]
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule trailing w).rhs (countEnv w x)).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases trailing <;> rcases width with rfl | rfl
      all_goals simp only [countRule,countEnv,Bool.false_eq_true,ite_false,ite_true,
        Nat.reduceEqDiff,false_or,or_false,true_or,or_true]
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
/-- Actual successful ctz narrow execution derives its guarded mapped source request. -/
theorem stock_count_ctz_narrow_requests {p : Program} (hp : Data p) (ctx : Ctx) 
    {w x n : Nat} (width : w = 8 ∨ w = 16)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule true w).rhs (env1 (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule true w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (countRule true w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
/-- Actual successful clz narrow execution derives its guarded mapped source request. -/
theorem stock_count_clz_narrow_requests {p : Program} (hp : Data p) (ctx : Ctx) 
    {w x n : Nat} (width : w = 8 ∨ w = 16) (typed : ctx.valueType? x = some (.int w))
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  have getTy := ext_value_type ctx st.base typed
  have fits := ext_fits_in_32_ty ctx st.base (.int w)
  have small : (.int w : CTy).bits ≤ 32 := by rcases width with rfl | rfl <;> decide
  simp only [small,ite_true] at fits
  have not32 : (V.ty (.int w) == V.ty (.int 32)) = false := by rcases width with rfl | rfl <;> decide
  have not64 : (V.ty (.int w) == V.ty (.int 64)) = false := by rcases width with rfl | rfl <;> decide
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl
      all_goals isel_eval [*,countRule,countEnv,rule_lower_1951,rule_lower_1955,rule_lower_1961,
        rule_lower_1982,rule_lower_1986,rule_lower_1995,rule_inst_3809,rule_inst_3813,rule_inst_3814,
        sem_ctor,sem_extract,sem_unData,sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok pair =>
    obtain ⟨v,q⟩ := pair
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v q).mp request
    exact ⟨safe,rx,mapped⟩
/-- Successful narrow CLZ establishes that its extension read an actual
context type; frame consistency identifies that type during source transfer. -/
theorem stock_count_clz_narrow_type {p : Program} (hp : Data p) (ctx : Ctx)
    {w x n : Nat} (width : w = 8 ∨ w = 16)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    ∃ t,ctx.valueType? x = some t := by
  cases typed : ctx.valueType? x with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have missing := ext_value_type_none ctx st.base typed
    have denied : (evalExpr p (Stock.sem ctx) {} (n+80) (countRule false w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl
      all_goals isel_eval [*,countRule,rule_lower_1951,rule_lower_1955,
        rule_inst_3809,rule_inst_3813,rule_inst_3814,sem_ctor,sem_extract,sem_unData,
        sem_eq,sem_prim,sem_bool,sem_int16,sem_int24,sem_int32]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
end Backend.Stock.Proof.ScalarCount

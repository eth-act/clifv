import FV.Backend.Proof.StockValues
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockHighMulPure
import FV.Backend.Proof.IselTermsALUAMulN
namespace Backend.Stock.Proof.ScalarHighMul
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
def wideRule (signed : Bool) : Rule := if signed then rule_lower_1056 else rule_lower_1068
def wideEnv (x y : Nat) : Isle.Interp.Env V := env2a (.value x) (.value y)
theorem stock_highmul_wide_helper {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    (st : State) (tr : Array RuleId) (n : Nat) (rx ry : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 (if signed then 452 else 451)
      [.ty (.int 64),.reg rx,.reg ry]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRR (if signed then .sMulH else .uMulH)
          .size64 (st.base.fresh .int).1 rx ry)},
        ((tr.push rule_inst_1593.id).push rule_inst_2545.id).push
          (if signed then rule_inst_3218.id else rule_inst_3213.id)) := by
  cases signed
  · exact stock_highmul_pure_helper hp ctx rfl (by decide)
      (umulh_run hp ctx (cfg := {}) rfl st.base tr n rx ry)
  · exact stock_highmul_pure_helper hp ctx rfl (by decide)
      (smulh_run hp ctx (cfg := {}) rfl st.base tr n rx ry)
/-- Actual64-bit roots derive their complete marked scheduling/emission state
from the two guarded original-source requests. -/
theorem stock_highmul_wide_rhs {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x y : Nat} {rx ry : Reg} (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+50) (wideRule signed).rhs (wideEnv x y)).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {(st.mark x).mark y with base := ((st.base.fresh .int).2.emit
          (.aluRRR (if signed then .sMulH else .uMulH) .size64 (st.base.fresh .int).1 rx ry))},trace) := by
  have requestX := stock_put_in_reg ctx st x rx mapX safeX
  have requestY := stock_put_in_reg ctx (st.mark x) y ry mapY safeY
  have helper := fun q trace fuel => stock_highmul_wide_helper hp ctx signed q trace fuel rx ry
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have primitive : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [wideRule,wideEnv,Bool.false_eq_true,ite_false] at *
      isel_eval [*,rule_lower_1068,sem_ctor,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [wideRule,wideEnv,ite_true] at *
      isel_eval [*,rule_lower_1056,sem_ctor,sem_mkData]
      all_goals rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_bool (ctx : Ctx) (b : Bool) : (Stock.sem ctx).bool b = .bool b := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) : (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
theorem stock_highmul_extend_reg {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (signed : Bool) (w : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+20) 27 417 [.reg rx,.bool signed,.int w,.int 64]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx signed w 64)},
        tr.push rule_inst_2991.id) := by
  exact stock_highmul_pure_helper hp ctx rfl (by decide)
    (extend_run_fa hp ctx (cfg := {}) rfl st.base tr n rx signed w 64)
/-- The actual narrow widening helpers demand the original operand and retain
all scheduling fields while allocating their64-bit temporary. -/
theorem stock_highmul_extend_request {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x w : Nat} (width : w ≤ 32) (type : ctx.valueType? x = some (.int w))
    {rx : Reg} (mapped : ctx.valueReg? x = some rx) (st : State) (safe : DemandAllowed ctx st x)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(applyTerm p (Stock.sem ctx) {} (n+60) 27 (if signed then 557 else 558) [.value x]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st.mark x with base := (st.base.fresh .int).2.emit (.extend (st.base.fresh .int).1 rx signed w 64)},trace) := by
  have helper := fun q trace fuel => stock_highmul_extend_reg hp ctx q trace fuel rx signed w
  have valueType := ext_value_type ctx st.base type
  have fits := ext_fits_in_32_ty_fa ctx st.base (.int w)
  simp only [CTy.bits,width,ite_true] at fits
  have bits : ∀ q,Stock.externCtor ctx T.ty_bits [.ty (.int w)] q = .ok (.int w,q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.ty_bits _ q (by decide)]
    rfl
  have request := stock_put_in_reg ctx st x rx mapped safe
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [Bool.false_eq_true,ite_false] at *
      isel_eval [*,rule_inst_3829,rule_inst_3833,sem_ctor,sem_extract,sem_bool,sem_int,ctor_ty_bits_ty_fa]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [ite_true] at *
      isel_eval [*,rule_inst_3819,rule_inst_3823,sem_ctor,sem_extract,sem_bool,sem_int,ctor_ty_bits_ty_fa]
      all_goals rfl
theorem stock_highmul_shift_helper {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    (st : State) (tr : Array RuleId) (n : Nat) (rx : Reg) (amount : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 (if signed then 487 else 489)
      [.ty (.int 64),.reg rx,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmShift (if signed then .asr else .lsr)
          .size64 (st.base.fresh .int).1 rx amount)},
        ((tr.push rule_inst_1593.id).push rule_inst_2537.id).push
          (if signed then rule_inst_3366.id else rule_inst_3375.id)) := by
  cases signed
  · exact stock_highmul_pure_helper hp ctx rfl (by decide)
      (lsr_imm_run hp ctx (cfg := {}) rfl st.base tr n rx amount)
  · exact stock_highmul_pure_helper hp ctx rfl (by decide)
      (asr_imm_run hp ctx (cfg := {}) rfl st.base tr n rx amount)
end Backend.Stock.Proof.ScalarHighMul

import FV.Backend.Proof.StockHighMulRhs
import FV.Backend.Proof.StockMulHelper
namespace Backend.Stock.Proof.ScalarHighMul
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_int (ctx : Ctx) (ty : Nat) (i : Int) :
    (Stock.sem ctx).int ty i = .int (normInt ty i) := rfl
private theorem sem_prim (ctx : Ctx) : (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl
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
def narrowRule (signed : Bool) : Rule := if signed then rule_lower_1059 else rule_lower_1071
def narrowEnv (w x y : Nat) : Isle.Interp.Env V := env7 (.ty (.int w)) (.value x) (.value y)
def multiplyBase (b : LState) (rx ry : Reg) : LState :=
  (b.fresh .int).2.emit (.aluRRRR .mAdd .size64 (b.fresh .int).1 rx ry .xzr)
def finishBase (signed : Bool) (w : Nat) (b : LState) (rx ry : Reg) : LState :=
  ((multiplyBase b rx ry).fresh .int).2.emit
    (.aluRRImmShift (if signed then .asr else .lsr) .size64 ((multiplyBase b rx ry).fresh .int).1 (b.fresh .int).1 w)
/-- Actual narrow roots compose the two real widening-helper runs with the
multiply/shift/output runs, preserving complete Stock scheduling state. -/
theorem stock_highmul_narrow_from_parts {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x y w : Nat} (width : w ≤ 32) (st : State) (tr : Array RuleId) (n : Nat)
    {rx ry : Reg} {s1 s2 : State} {t1 t2 : Array RuleId}
    (first : (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 557 else 558) [.value x]).run (st,tr) = .ok (some (.reg rx),s1,t1))
    (second : (applyTerm p (Stock.sem ctx) {} (n+96) 27 (if signed then 557 else 558) [.value y]).run (s1,t1) = .ok (some (.reg ry),s2,t2)) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100) (narrowRule signed).rhs (narrowEnv w x y)).run (st,tr) =
      .ok (some (.regsVec [[((multiplyBase s2.base rx ry).fresh .int).1]]),
        {s2 with base := finishBase signed w s2.base rx ry},trace) := by
  have mul := fun q trace fuel => ScalarMul.stock_madd_helper hp ctx (cfg := {}) rfl
    (w := 64) (by decide) q trace fuel rx ry .xzr
  have shift := fun q trace fuel => stock_highmul_shift_helper hp ctx signed q trace fuel
    (s2.base.fresh .int).1 w
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have zero : ∀ q,Stock.externCtor ctx T.zero_reg [] q = .ok (.reg .xzr,q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.zero_reg _ q (by decide)]; rfl
  have bits : ∀ q,Stock.externCtor ctx T.ty_bits [.ty (.int w)] q = .ok (.int w,q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.ty_bits _ q (by decide)]; rfl
  have immediate : ∀ q,Stock.externCtor ctx T.imm_shift_from_u8 [.int w] q = .ok (.op (.immShift w),q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.imm_shift_from_u8 _ q (by decide)]
    rw [ctor_imm_shift_from_u8 ctx q.base (n := (w : Int)) (by omega)]
    rfl
  have value : ∀ q r,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q r; rw [stock_ctor_baseOnly ctx T.value_reg _ q (by decide)]; rfl
  have rawOutput : ∀ q r,Stock.externCtor ctx T.output [.regs [r]] q = .ok (.regsVec [[r]],q) := by
    intro q r; rw [stock_ctor_baseOnly ctx T.output _ q (by decide)]; rfl
  cases hp
  cases signed
  · refine Exists.intro ?traceU ?proofU
    case proofU =>
      simp only [narrowRule,narrowEnv,Bool.false_eq_true,ite_false] at *
      isel_eval [*,rule_lower_1071,sem_ctor,sem_int,sem_prim,sem_mkData]
      all_goals rfl
  · refine Exists.intro ?traceS ?proofS
    case proofS =>
      simp only [narrowRule,narrowEnv,ite_true] at *
      isel_eval [*,rule_lower_1059,sem_ctor,sem_int,sem_prim,sem_mkData]
      all_goals rfl
def extendBase (b : LState) (signed : Bool) (w : Nat) (r : Reg) : LState :=
  (b.fresh .int).2.emit (.extend (b.fresh .int).1 r signed w 64)
def narrowBase (b : LState) (signed : Bool) (w : Nat) (rx ry : Reg) : LState :=
  let b1 := extendBase b signed w rx
  let b2 := extendBase b1 signed w ry
  finishBase signed w b2 (b.fresh .int).1 (b1.fresh .int).1
/-- Full narrow RHS execution derives both widening runs from original guarded
requests and preserves the exact complete marked state across all four writes. -/
theorem stock_highmul_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx) (signed : Bool)
    {x y w : Nat} (width : w ≤ 32)
    (typeX : ctx.valueType? x = some (.int w)) (typeY : ctx.valueType? y = some (.int w))
    {rx ry : Reg} (mapX : ctx.valueReg? x = some rx) (mapY : ctx.valueReg? y = some ry)
    (st : State) (safeX : DemandAllowed ctx st x) (safeY : DemandAllowed ctx st y)
    (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+100) (narrowRule signed).rhs (narrowEnv w x y)).run (st,tr) =
      .ok (some (.regsVec [[((multiplyBase (extendBase (extendBase st.base signed w rx) signed w ry)
        (st.base.fresh .int).1 ((extendBase st.base signed w rx).fresh .int).1).fresh .int).1]]),
        {(st.mark x).mark y with base := narrowBase st.base signed w rx ry},trace) := by
  obtain ⟨t1,first⟩ := stock_highmul_extend_request hp ctx signed width typeX mapX st safeX tr (n+37)
  let s1 : State := {st.mark x with base := extendBase st.base signed w rx}
  change (applyTerm p (Stock.sem ctx) {} (n+97) 27 (if signed then 557 else 558) [.value x]).run (st,tr) =
    .ok (some (.reg (st.base.fresh .int).1),s1,t1) at first
  obtain ⟨t2,second⟩ := stock_highmul_extend_request hp ctx signed width typeY mapY s1 safeY t1 (n+36)
  let s2 : State := {(st.mark x).mark y with base := extendBase (extendBase st.base signed w rx) signed w ry}
  change (applyTerm p (Stock.sem ctx) {} (n+96) 27 (if signed then 557 else 558) [.value y]).run (s1,t1) =
    .ok (some (.reg ((extendBase st.base signed w rx).fresh .int).1),s2,t2) at second
  exact stock_highmul_narrow_from_parts hp ctx signed width st tr n first second
end Backend.Stock.Proof.ScalarHighMul

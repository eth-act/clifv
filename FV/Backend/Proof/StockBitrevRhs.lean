import FV.Backend.Proof.StockRequestSuccess
import FV.Backend.Proof.StockShiftHelper
import FV.Backend.Proof.StockBitHelper
namespace Backend.Stock.Proof.ScalarBit
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
  have inner := fun q trace fuel => stock_bit_rr_helper hp ctx (cfg := {}) rfl small (k := 0) (op := .rbit) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3512,sem_mkData]
private theorem lsr_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) (amount : Nat) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 489 [.ty (.int 32),.reg r,.op (.immShift amount)]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.aluRRImmShift .lsr .size32 (st.base.fresh .int).1 r amount)},
        ((tr.push rule_inst_1592.id).push rule_inst_2537.id).push rule_inst_3375.id) := by
  have inner := fun q trace fuel => ScalarShift.stock_shift_imm_helper hp ctx (cfg := {}) rfl (w := 32) (k := 16) (op := .lsr) (by decide) rfl q trace fuel r amount
  cases hp
  isel_eval [*,rule_inst_3375,sem_mkData]
  rfl
private theorem shift16 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.imm_shift_from_u8 [.int 16] st = .ok (.op (.immShift 16),st) := by
  rw [stock_ctor_baseOnly ctx T.imm_shift_from_u8 _ st (by decide)]
  rfl
private theorem shift24 (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.imm_shift_from_u8 [.int 24] st = .ok (.op (.immShift 24),st) := by
  rw [stock_ctor_baseOnly ctx T.imm_shift_from_u8 _ st (by decide)]
  rfl
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
section Numbers
attribute [local semireducible] Isle.Aarch64.program
private theorem int24 (ctx : Ctx) : (Stock.sem ctx).int 1 24 = .int 24 := rfl
private theorem int16 (ctx : Ctx) : (Stock.sem ctx).int 1 16 = .int 16 := rfl
end Numbers

def bitrevNarrowRule (half : Bool) : Rule := if half then rule_lower_1937 else rule_lower_1931
def bitrevNarrowWidth (half : Bool) : Nat := if half then 16 else 8
def bitrevNarrowShift (half : Bool) : Nat := if half then 16 else 24
/-- Both narrow bit-reversal matches retain scheduling state and canonical source binding. -/
theorem stock_bitrev_narrow_match {p : Program} (hp : Data p) (ctx : Ctx) (half : Bool)
    {i x : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int (bitrevNarrowWidth half)))
    (data : info.data = .data 152 29 [.data 151 106 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (bitrevNarrowRule half) [.inst i]).run (st,tr) =
      .ok (some (env1 (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  cases half <;> isel_eval [*,bitrevNarrowRule,bitrevNarrowWidth,rule_lower_1931,rule_lower_1937,sem_extract,sem_unData,sem_eq,sem_prim]
/-- The fallback bit-reversal matcher supplies its actual width/source environment. -/
theorem stock_bitrev_wide_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 106 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_1946 [.inst i]).run (st,tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  isel_eval [*,rule_lower_1946,sem_extract,sem_unData]
/-- Actual fallback RHS requests the mapped source and emits one rbit. -/
theorem stock_bitrev_wide_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w ≤ 64) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_1946.rhs
      (env2 (.ty (.int w)) (.value x))).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (.bitRR .rbit (szOf w) (st.base.fresh .int).1 rx)},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have bit := fun q trace fuel r => rbit_run hp ctx width q trace fuel r
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof => isel_eval [*,rule_lower_1946,sem_ctor]; rfl
/-- Actual byte/halfword RHS marks its operand once, then emits rbit and logical shift. -/
theorem stock_bitrev_narrow_rhs {p : Program} (hp : Data p) (ctx : Ctx) (half : Bool)
    {x : Nat} {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (bitrevNarrowRule half).rhs (env1 (.value x))).run (st,tr) =
      .ok (some (.regsVec [[.vreg (st.base.nextVreg+1) .int]]),
        {st.mark x with base := (((st.base.fresh .int).2.emit (.bitRR .rbit .size32 (st.base.fresh .int).1 rx)).fresh .int).2.emit (.aluRRImmShift .lsr .size32 (.vreg (st.base.nextVreg+1) .int) (st.base.fresh .int).1 (bitrevNarrowShift half))},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have bit := fun q trace fuel r => rbit_run hp ctx (w := 32) (by decide) q trace fuel r
  have shift := fun q trace fuel r amount => lsr_run hp ctx q trace fuel r amount
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  have imm16 := fun q => shift16 ctx q
  have imm24 := fun q => shift24 ctx q
  cases hp
  cases half
  · refine Exists.intro ?trace8 ?proof8
    case proof8 =>
      isel_eval [*,bitrevNarrowRule,bitrevNarrowShift,rule_lower_1931,sem_ctor,sem_prim,int24]
      rfl
  · refine Exists.intro ?trace16 ?proof16
    case proof16 =>
      isel_eval [*,bitrevNarrowRule,bitrevNarrowShift,rule_lower_1937,sem_ctor,sem_prim,int16]
      rfl
/-- A successful actual wide bit-reversal RHS supplies its guarded mapped request. -/
theorem stock_bitrev_wide_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {x w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_1946.rhs (env2 (.ty (.int w)) (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases requested : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_1946.rhs (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_1946,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_1946.rhs (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_1946,sem_ctor]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
/-- A successful actual narrow bit-reversal RHS supplies its guarded mapped request. -/
theorem stock_bitrev_narrow_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    (half : Bool) {x n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (bitrevNarrowRule half).rhs (env1 (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases requested : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (bitrevNarrowRule half).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases half <;> isel_eval [*,bitrevNarrowRule,rule_lower_1931,rule_lower_1937,sem_ctor,sem_prim,int16,int24]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (bitrevNarrowRule half).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      cases half <;> isel_eval [*,bitrevNarrowRule,rule_lower_1931,rule_lower_1937,sem_ctor,sem_prim,int16,int24]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarBit

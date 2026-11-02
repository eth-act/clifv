import FV.Backend.Proof.StockRequestSuccess
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
private theorem sem_eq (ctx : Ctx) (a b : V) : (Stock.sem ctx).eq a b = (a == b) := rfl
private theorem sem_prim (ctx : Ctx) (name : String) :
    (Stock.sem ctx).prim 14 name = (CTy.ofName? name).map V.ty := rfl
private theorem rev16_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 520 [.ty (.int 16),.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitRR .rev16 .size32 (st.base.fresh .int).1 r)},
        ((tr.push rule_inst_1592.id).push rule_inst_2733.id).push rule_inst_3527.id) := by
  have inner := fun q trace fuel => stock_bit_rr_helper hp ctx (cfg := {}) rfl (w := 16) (k := 3) (op := .rev16) (by decide) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3527,sem_mkData]
  rfl
private theorem rev32_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 521 [.ty (.int 32),.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitRR .rev32 .size32 (st.base.fresh .int).1 r)},
        ((tr.push rule_inst_1592.id).push rule_inst_2733.id).push rule_inst_3531.id) := by
  have inner := fun q trace fuel => stock_bit_rr_helper hp ctx (cfg := {}) rfl (w := 32) (k := 4) (op := .rev32) (by decide) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3531,sem_mkData]
  rfl
private theorem rev64_run {p : Program} (hp : Data p) (ctx : Ctx)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 522 [.ty (.int 64),.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.bitRR .rev64 .size64 (st.base.fresh .int).1 r)},
        ((tr.push rule_inst_1593.id).push rule_inst_2733.id).push rule_inst_3535.id) := by
  have inner := fun q trace fuel => stock_bit_rr_helper hp ctx (cfg := {}) rfl (w := 64) (k := 5) (op := .rev64) (by decide) rfl q trace fuel r
  cases hp
  isel_eval [*,rule_inst_3535,sem_mkData]
  rfl
def bswapRule (w : Nat) : Rule := if w = 16 then rule_lower_2035 else if w = 32 then rule_lower_2038 else rule_lower_2041
def bswapOp (w : Nat) : BitOp := if w = 16 then .rev16 else if w = 32 then .rev32 else .rev64
/-- Actual byte-swap matching retains complete scheduling state and trace. -/
theorem stock_bswap_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x w : Nat} {info : IInfo} (width : w = 16 ∨ w = 32 ∨ w = 64)
    (source : ctx.insts[i]? = some info) (type : info.resTys.head? = some (.int w))
    (data : info.data = .data 152 29 [.data 151 110 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) (bswapRule w) [.inst i]).run (st,tr) =
      .ok (some (env1 (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  cases hp
  rcases width with rfl | rfl | rfl
  all_goals isel_eval [*,bswapRule,rule_lower_2035,rule_lower_2038,rule_lower_2041,sem_extract,sem_unData,sem_prim,sem_eq]
/-- Actual byte-swap RHS marks its mapped source and emits one fresh result. -/
theorem stock_bswap_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w = 16 ∨ w = 32 ∨ w = 64) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) (bswapRule w).rhs (env1 (.value x))).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (.bitRR (bswapOp w) (szOf w) (st.base.fresh .int).1 rx)},trace) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have rev16 := fun q trace fuel r => rev16_run hp ctx q trace fuel r
  have rev32 := fun q trace fuel r => rev32_run hp ctx q trace fuel r
  have rev64 := fun q trace fuel r => rev64_run hp ctx q trace fuel r
  have output := fun q trace fuel r => output_run hp ctx q trace fuel r
  cases hp
  rcases width with rfl | rfl | rfl
  · refine Exists.intro ?trace16 ?proof16
    case proof16 =>
      isel_eval [*,bswapRule,bswapOp,szOf,rule_lower_2035,sem_ctor,sem_prim]
      rfl
  · refine Exists.intro ?trace32 ?proof32
    case proof32 =>
      isel_eval [*,bswapRule,bswapOp,szOf,rule_lower_2038,sem_ctor,sem_prim]
      rfl
  · refine Exists.intro ?trace64 ?proof64
    case proof64 =>
      isel_eval [*,bswapRule,bswapOp,szOf,rule_lower_2041,sem_ctor,sem_prim]
      rfl
/-- Success derives the guarded mapped request used by the actual RHS. -/
theorem stock_bswap_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {x w n : Nat} (width : w = 16 ∨ w = 32 ∨ w = 64)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) (bswapRule w).rhs (env1 (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases requested : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (bswapRule w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl | rfl
      all_goals isel_eval [*,bswapRule,rule_lower_2035,rule_lower_2038,rule_lower_2041,sem_ctor,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) (bswapRule w).rhs (env1 (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      rcases width with rfl | rfl | rfl
      all_goals isel_eval [*,bswapRule,rule_lower_2035,rule_lower_2038,rule_lower_2041,sem_ctor,sem_prim]
      all_goals intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarBit

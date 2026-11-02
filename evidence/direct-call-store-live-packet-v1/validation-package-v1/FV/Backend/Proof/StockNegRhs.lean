import FV.Backend.Proof.StockRequestSuccess
namespace Backend.Stock.Proof.Neg
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
private theorem zero_reg (ctx : Ctx) (st : State) :
    Stock.externCtor ctx T.zero_reg [] st = .ok (.reg .xzr,st) := by
  rw [stock_ctor_baseOnly ctx T.zero_reg _ st (by decide)]; rfl
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
private theorem sub_zero {p : Program} (hp : Data p) (ctx : Ctx) {w : Nat} (width : w ≤ 64)
    (st : State) (tr : Array RuleId) (n : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) {} (n+30) 27 437 [.ty (.int w),.reg .xzr,.reg r]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),{st with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 .xzr r)},
        ((tr.push (if w ≤ 32 then rule_inst_1592.id else rule_inst_1593.id)).push rule_inst_2545.id).push rule_inst_3138.id) := by
  have inner := fun q trace fuel => stock_alu_rrr_helper hp ctx (cfg := {}) rfl width (k := 1) (op := .sub) rfl q trace fuel .xzr r
  cases hp
  isel_eval [*,rule_inst_3138,sem_mkData]
/-- Actual scalar negation matching preserves the complete scheduling state. -/
theorem stock_neg_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (small : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 75 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+2) rule_lower_857 [.inst i]).run (st,tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have fits := ext_fits_in_64 ctx st.base w
  simp only [small,ite_true] at fits
  cases hp
  isel_eval [*,rule_lower_857,sem_extract,sem_unData]
/-- The real scalar negation RHS marks its mapped operand, then allocates and
emits one subtraction from zero, retaining the other scheduling fields. -/
theorem stock_neg_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} (width : w ≤ 64) {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    ∃ trace,(evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_857.rhs
      (env2 (.ty (.int w)) (.value x))).run (st,tr) =
      .ok (some (.regsVec [[(st.base.fresh .int).1]]),
        {st.mark x with base := (st.base.fresh .int).2.emit (.aluRRR .sub (szOf w) (st.base.fresh .int).1 .xzr rx)},trace) := by
  have requested := stock_put_in_reg ctx st x rx mapped safe
  have zero := fun q => zero_reg ctx q
  have sub := fun q tr n => sub_zero hp ctx width q tr n rx
  have output := fun q tr n r => output_run hp ctx q tr n r
  cases hp
  refine Exists.intro ?trace ?proof
  case proof =>
    isel_eval [*,rule_lower_857,sem_ctor]
    rfl
/-- Successful actual negation RHS supplies its unsunk mapped request. -/
theorem stock_neg_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {x w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_857.rhs
      (env2 (.ty (.int w)) (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  have zero := fun q => zero_reg ctx q
  cases requested : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_857.rhs
        (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_857,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_857.rhs
        (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_857,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (stock_put_in_reg_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.Neg

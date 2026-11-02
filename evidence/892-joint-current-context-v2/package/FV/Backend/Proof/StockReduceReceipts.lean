import FV.Backend.Proof.StockProjection
import FV.Backend.Proof.IselFamAluBMisc
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.StockShiftRequests
namespace Backend.Stock.Proof.ScalarCast.Reduce
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl
private theorem sem_unData (ctx : Ctx) (t : Nat) (v : V) :
    (Stock.sem ctx).unData t v = (Backend.sem ctx).unData t v := rfl
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_int (ctx : Ctx) (t : Nat) (z : Int) : (Stock.sem ctx).int t z = .int (normInt t z) := rfl
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
/-- The actual reduction matcher and scalar-type guard retain all scheduling
state and trace, with the original typed source environment. -/
theorem stock_reduce_match {p : Program} (hp : Data p) (ctx : Ctx)
    {i x w : Nat} {info : IInfo} (source : ctx.insts[i]? = some info)
    (type : info.resTys.head? = some (.int w)) (small : w ≤ 64)
    (data : info.data = .data 152 29 [.data 151 131 [],.value x])
    (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+10) rule_lower_2146 [.inst i]).run (st,tr) =
      .ok (some (env2 (.ty (.int w)) (.value x)),st,tr) := by
  have extraction := ext_inst_data_value ctx st.base source
  rw [data,type,Option.getD_some] at extraction
  have scalar : ∀ q,Stock.externCtor ctx T.ty_int_ref_scalar_64 [.ty (.int w)] q = .ok (.ty (.int w),q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.ty_int_ref_scalar_64 _ q (by decide)]
    rw [ctor_ty_int_ref_scalar_64 ctx q.base small]
  cases hp
  isel_eval [*,rule_lower_2146,sem_extract,sem_unData,sem_ctor]
/-- A successful reduction request marks its source and returns that same
register through the real output wrapper, with no emitted code or allocation. -/
theorem stock_reduce_rhs {p : Program} (hp : Data p) (ctx : Ctx)
    {x w : Nat} {rx : Reg} (mapped : ctx.valueReg? x = some rx)
    (st : State) (safe : DemandAllowed ctx st x) (tr : Array RuleId) (n : Nat) :
    (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_2146.rhs (env2 (.ty (.int w)) (.value x))).run (st,tr) =
      .ok (some (.regsVec [[rx]]),st.mark x,tr.push rule_prelude_lower_105.id) := by
  have requested := stock_put_in_regs ctx st x rx mapped safe
  have get : ∀ q,Stock.externCtor ctx T.value_regs_get [.regs [rx],.int 0] q = .ok (.reg rx,q) := by
    intro q; rw [stock_ctor_baseOnly ctx T.value_regs_get _ q (by decide)]; rfl
  have output := fun q tr n r => output_run hp ctx q tr n r
  cases hp
  isel_eval [*,rule_lower_2146,sem_ctor,sem_int]
/-- Successful actual reduction RHS evaluation supplies its unsunk mapped
source request internally. -/
theorem stock_reduce_rhs_requests {p : Program} (hp : Data p) (ctx : Ctx)
    {x w n : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_2146.rhs
      (env2 (.ty (.int w)) (.value x))).run (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx := by
  cases requested : Stock.externCtor ctx T.put_in_regs [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_2146.rhs
        (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_2146,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled err =>
    have denied : (evalExpr p (Stock.sem ctx) {} (n+40) rule_lower_2146.rhs
        (env2 (.ty (.int w)) (.value x))).run (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_lower_2146,sem_ctor]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨v,st'⟩ := result
    obtain ⟨safe,rx,mapped,_,_⟩ := (ScalarShift.stock_shift_put_in_regs_iff ctx st x v st').mp requested
    exact ⟨safe,rx,mapped⟩
end Backend.Stock.Proof.ScalarCast.Reduce

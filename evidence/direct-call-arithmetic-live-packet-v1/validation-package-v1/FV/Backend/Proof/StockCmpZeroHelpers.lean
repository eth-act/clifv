import FV.Backend.Proof.StockRequestSuccess
namespace Backend.Stock.Proof.ScalarCmp
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty t k : Nat) (vs : List V) :
    (Stock.sem ctx).unData ty (.data t k vs) = if t = ty then some (k,vs) else none :=
  Backend.Proof.sem_unData ctx ty t k vs
/-- The real inversion helper switches Zero/NotZero while preserving every Stock field. -/
theorem stock_cmp_zero_invert {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (nonzero : Bool) (r : Reg) (size : V)
    (st : State) (tr : Array RuleId) (n : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (n+40) 123 649
      [.data 123 (if nonzero then 1 else 0) [.reg r,size]]).run (st,tr) =
      .ok (some (.data 123 (if nonzero then 0 else 1) [.reg r,size]),st,
        tr.push (if nonzero then rule_inst_4955.id else rule_inst_4954.id)) := by
  cases hp
  cases nonzero <;>
    isel_eval [*,rule_inst_4954,rule_inst_4955,rule_inst_4956,rule_inst_4957,rule_inst_4959,
      sem_mkData,sem_unData]
/-- Actual successful inversion supplies the switched condition and unchanged full state. -/
theorem stock_cmp_zero_invert_observed {p : Program} (hp : Data p) (ctx : Ctx)
    {fuel : Nat} (enough : 39 ≤ fuel) (nonzero : Bool) (r : Reg) (size : V)
    {st next : State} {tr trace : Array RuleId} {out : V}
    (run : ApplyInternal p (Stock.sem ctx) {} fuel 123 649
      [.data 123 (if nonzero then 1 else 0) [.reg r,size]] (st,tr) out (next,trace)) :
    out = .data 123 (if nonzero then 0 else 1) [.reg r,size] ∧ next = st := by
  obtain ⟨n,equal⟩ : ∃ n,fuel+1=n+40 := ⟨fuel-39,by omega⟩
  unfold ApplyInternal at run
  rw [equal,stock_cmp_zero_invert hp ctx rfl nonzero r size st tr n] at run
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at run
  exact ⟨run.1.symm,run.2.1.symm⟩
/-- The real64-bit nonzero RHS requests its original operand and retains the complete marked state. -/
theorem stock_cmp_nonzero64_rhs {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (x : Nat) (rx : Reg) (st : State) (tr : Array RuleId) (n : Nat)
    (mapped : ctx.valueReg? x = some rx) (safe : DemandAllowed ctx st x) :
    (evalExpr p (Stock.sem ctx) cfg (n+30) rule_inst_4979.rhs #[some (.value x)]).run (st,tr) =
      .ok (some (.data 123 1 [.reg rx,.data 93 1 []]),st.mark x,tr) := by
  have request := stock_put_in_reg ctx st x rx mapped safe
  have get : (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) := rfl
  cases hp
  isel_eval [*,rule_inst_4979,sem_ctor,sem_mkData]
/-- A successful real64-bit nonzero RHS supplies its original demand guard,
mapped register, exact condition and full marked state internally. -/
theorem stock_cmp_nonzero64_rhs_observed {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {n x : Nat} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr p (Stock.sem ctx) cfg (n+30) rule_inst_4979.rhs #[some (.value x)]).run
      (st,tr) = .ok (some out,next,trace)) :
    DemandAllowed ctx st x ∧ ∃ rx,ctx.valueReg? x = some rx ∧
      out = .data 123 1 [.reg rx,.data 93 1 []] ∧ next = st.mark x := by
  have get : (#[some (.value x)] : Isle.Interp.Env V)[0]? = some (some (.value x)) := rfl
  cases request : Stock.externCtor ctx T.put_in_reg [.value x] st with
  | fail =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+30) rule_inst_4979.rhs #[some (.value x)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_4979,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | unmodeled e =>
    have denied : (evalExpr p (Stock.sem ctx) cfg (n+30) rule_inst_4979.rhs #[some (.value x)]).run
        (st,tr) ≠ .ok (some out,next,trace) := by
      cases hp
      isel_eval [*,rule_inst_4979,sem_ctor,sem_mkData]
      intro impossible; cases impossible
    exact False.elim (denied run)
  | ok result =>
    obtain ⟨value,after⟩ := result
    obtain ⟨safe,rx,mapped,rfl,rfl⟩ := (stock_put_in_reg_iff ctx st x value after).mp request
    have replay := stock_cmp_nonzero64_rhs hp ctx hc x rx st tr n mapped safe
    rw [run] at replay
    simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at replay
    exact ⟨safe,rx,mapped,replay.1,replay.2.1⟩
private def fixtureCtx : Ctx := {sinkCtx with valDef := #[none],valReg := #[some (.vreg 7 .int)]}
/-- An actual source request and nonzero condition inhabit the observed RHS contract. -/
theorem stock_cmp_nonzero64_rhs_witness :
    ∃ out next trace,(evalExpr program (Stock.sem fixtureCtx) {} 1000 rule_inst_4979.rhs #[some (.value 0)]).run
      (sinkState,#[]) = .ok (some out,next,trace) ∧ DemandAllowed fixtureCtx sinkState 0 := by
  have safe : DemandAllowed fixtureCtx sinkState 0 := by
    intro j impossible
    change none = some j at impossible
    cases impossible
  exact ⟨_,_,_,stock_cmp_nonzero64_rhs data_program fixtureCtx (cfg := {}) rfl 0 (.vreg 7 .int)
    sinkState #[] 970 rfl safe,safe⟩
/-- Actual inversion and guarded64-bit nonzero emission have inhabited inputs. -/
theorem stock_cmp_zero_helpers_witness (nonzero : Bool) (sz : OperandSize) :
    ∃ out trace,(applyTerm program (Stock.sem sinkCtx) {} 1000 123 649
      [.data 123 (if nonzero then 1 else 0) [.reg (.vreg 7 .int),.data 93 (if sz = .size32 then 0 else 1) []]]).run
      (sinkState,#[]) = .ok (some out,sinkState,trace) := by
  exact ⟨_,_,stock_cmp_zero_invert data_program sinkCtx (cfg := {}) rfl nonzero (.vreg 7 .int)
    (.data 93 (if sz = .size32 then 0 else 1) []) sinkState #[] 960⟩
end Backend.Stock.Proof.ScalarCmp

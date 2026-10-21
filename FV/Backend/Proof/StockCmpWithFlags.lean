import FV.Backend.Proof.StockCmpBuilders
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
/-- The actual side-effect flag producer/register consumer path emits both
instructions and retains all scheduling fields; no pure-full-closure claim. -/
theorem stock_cmp_with_flags_reg {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    {mi ci : V} {m1 m2 : MInst} (producer : MInst.ofV mi = some m1) (consumer : MInst.ofV ci = some m2) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (n+50) 22 254 [.data 47 1 [mi],.data 49 3 [ci,.reg r]]).run (st,tr) =
      .ok (some (.regs [r]),{st with base := (st.base.emit m1).emit m2},tr.push rule_prelude_lower_818.id) := by
  have emitProducer : ∀ q : State,Stock.externCtor ctx T.emit [mi] q =
      .ok (.op .unit,{q with base := q.base.emit m1}) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.emit [mi] q (by decide),ctor_emit ctx q.base producer]
  have emitConsumer : ∀ q : State,Stock.externCtor ctx T.emit [ci] q =
      .ok (.op .unit,{q with base := q.base.emit m2}) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.emit [ci] q (by decide),ctor_emit ctx q.base consumer]
  have value : ∀ q : State,Stock.externCtor ctx T.value_reg [.reg r] q = .ok (.regs [r],q) := by
    intro q
    rw [stock_ctor_baseOnly ctx T.value_reg [.reg r] q (by decide)]
    rfl
  cases hp
  isel_eval [*,rule_prelude_lower_789,rule_prelude_lower_798,rule_prelude_lower_807,rule_prelude_lower_812,rule_prelude_lower_818,stock_matchArgs,sem_ctor,sem_mkData,sem_unData]
end Backend.Stock.Proof.ScalarCmp

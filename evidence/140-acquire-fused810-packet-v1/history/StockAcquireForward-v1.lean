import FV.Backend.Proof.StockAcquireHelpers

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sem_ctor (ctx : Ctx) (term : Term) (args : List V) (st : State) :
    (Stock.sem ctx).ctor term args st = Stock.externCtor ctx term args st := rfl
private theorem sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- The actual acquire helper succeeds and emits one exact instruction.
All Stock scheduling fields remain unchanged. -/
theorem acquire_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) (ty : CTy) (flags : Clif.MemFlags) (address : Reg)
    (st : State) (trace : Array RuleId) (fuel : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+20) 27 422 [.ty ty,.op (.memFlags flags),.reg address]).run
      (st,trace) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit (.loadAcquire ty (st.base.fresh .int).1 address flags)},
        trace.push rule_inst_3028.id) := by
  have temp (s : State) : Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] s =
      .ok (.reg (s.base.fresh .int).1,{s with base := (s.base.fresh .int).2}) := rfl
  have reg (r : Reg) (s : State) : Stock.externCtor ctx T.writable_reg_to_reg [.reg r] s =
      .ok (.reg r,s) := rfl
  have emit (s : State) : Stock.externCtor ctx T.emit
      [.data 58 42 [.ty ty,.reg (st.base.fresh .int).1,.reg address,.op (.memFlags flags)]] s =
        .ok (.op .unit,{s with base := s.base.emit (.loadAcquire ty (st.base.fresh .int).1 address flags)}) := by
    rw [stock_ctor_baseOnly ctx T.emit _ s (by decide)]
    rfl
  cases hp
  isel_eval [*,rule_inst_3028,sem_ctor,sem_i64,temp,reg,emit]

end Backend.Stock.Proof.AcquireHelpers

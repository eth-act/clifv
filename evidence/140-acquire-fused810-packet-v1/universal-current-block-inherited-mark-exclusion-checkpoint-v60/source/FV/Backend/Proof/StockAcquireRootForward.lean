import FV.Backend.Proof.StockAcquireSinkForward

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The actual output helper wraps its register without changing any Stock field. -/
theorem output_reg_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) (st : State) (trace : Array RuleId) (fuel : Nat) (r : Reg) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+10) 25 172 [.reg r]).run (st,trace) =
      .ok (some (.regsVec [[r]]),st,trace.push rule_prelude_lower_105.id) := by
  have ctor (term : Term) (args : List V) (s : State) :
    (Stock.sem ctx).ctor term args s = Stock.externCtor ctx term args s := rfl
  have value_reg (s : State) : Stock.externCtor ctx T.value_reg [.reg r] s = .ok (.regs [r],s) := by
    rw [stock_ctor_baseOnly ctx T.value_reg _ s (by decide)]
    rfl
  have output (s : State) : Stock.externCtor ctx T.output [.regs [r]] s = .ok (.regsVec [[r]],s) := by
    rw [stock_ctor_baseOnly ctx T.output _ s (by decide)]
    rfl
  cases hp
  isel_eval [*,rule_prelude_lower_105,ctor,value_reg,output]

/-- The complete root810 RHS emits its acquire after the actual sink and address demand. -/
theorem acquire_rhs_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {ii pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (installed : ctx.insts[ii]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    {st sunk next : State} {address : Reg}
    (sink : Stock.externCtor ctx T.sink_inst [.inst ii] st = .ok (.op .unit,sunk))
    (demand : Stock.externCtor ctx T.put_in_reg [.value pointer] sunk = .ok (.reg address,next))
    {env : Isle.Interp.Env V} {ty : CTy}
    (inputTy : env[1]? = some (some (.ty ty)))
    (inputFlags : env[2]? = some (some (.op (.memFlags flags))))
    (producer : env[4]? = some (some (.inst ii)))
    (trace : Array RuleId) (fuel : Nat) :
    (evalExpr p (Stock.sem ctx) cfg (fuel+80) rule_lower_1272.rhs env).run (st,trace) =
      .ok (some (.regsVec [[(next.base.fresh .int).1]]),
        {next with base := (next.base.fresh .int).2.emit (.loadAcquire ty (next.base.fresh .int).1 address flags)},
        ((trace.push rule_inst_3905.id).push rule_inst_3028.id).push rule_prelude_lower_105.id) := by
  have sinkRun := fun trace fuel => sink_atomic_forward hp ctx overlap installed atomic sink demand trace fuel
  have acquireRun := fun st trace fuel => acquire_forward hp ctx overlap ty flags address st trace fuel
  have outputRun := fun st trace fuel r => output_reg_forward hp ctx overlap st trace fuel r
  cases hp
  isel_eval [*,rule_lower_1272]

end Backend.Stock.Proof.AcquireHelpers

import FV.Backend.Proof.StockMemoryHelperContracts
import FV.Backend.Proof.IselInterp

/-! Direct execution for the next integer-memory batch. -/
namespace Backend.Stock.Proof.MemoryHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

def IntegerLoad.ruleId : IntegerLoad → RuleId
  | .unsigned8 => 298 | .signed8 => 299 | .unsigned16 => 300 | .signed16 => 301
  | .unsigned32 => 302 | .signed32 => 303 | .unsigned64 => 304

def IntegerStore.ruleId : IntegerStore → RuleId
  | .bits8 => 310 | .bits16 => 311 | .bits32 => 312 | .bits64 => 313

private theorem sem_ctor (ctx : Ctx) (term : Term) (args : List V) (st : State) :
    (Stock.sem ctx).ctor term args st = Stock.externCtor ctx term args st := rfl
private theorem sem_mkData (ctx : Ctx) (ty tag : Nat) (args : List V) :
    (Stock.sem ctx).mkData ty tag args = .data ty tag args := rfl
private theorem sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- Every integer load helper succeeds when its emitted instruction decodes.
It allocates the exact fresh register and preserves every scheduling field. -/
theorem integer_load_forward (kind : IntegerLoad) {p : Program} (hp : Data p)
    (ctx : Ctx) {cfg : Config} (overlap : cfg.checkOverlap = false)
    (st : State) (trace : Array RuleId) (fuel : Nat) (address flags : V)
    (instruction : MInst)
    (decoded : MInst.ofV (.data 58 kind.tag
      [.reg (st.base.fresh .int).1,address,flags]) = some instruction) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+20) 27 kind.term [address,flags]).run
      (st,trace) = .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit instruction},trace.push kind.ruleId) := by
  have temp (s : State) : Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] s =
      .ok (.reg (s.base.fresh .int).1,{s with base := (s.base.fresh .int).2}) := rfl
  have reg (r : Reg) (s : State) : Stock.externCtor ctx T.writable_reg_to_reg [.reg r] s =
      .ok (.reg r,s) := rfl
  have emit (s : State) : Stock.externCtor ctx T.emit
      [.data 58 kind.tag [.reg (st.base.fresh .int).1,address,flags]] s =
        .ok (.op .unit,{s with base := s.base.emit instruction}) := by
    have legacy : Backend.externCtor ctx T.emit
        [.data 58 kind.tag [.reg (st.base.fresh .int).1,address,flags]] s.base =
          .ok (.op .unit,s.base.emit instruction) := by
      change (match MInst.ofV (.data 58 kind.tag
        [.reg (st.base.fresh .int).1,address,flags]) with
        | some i => ExtResult.ok (V.op .unit,s.base.emit i) | none => _) = _
      rw [decoded]
    rw [stock_ctor_baseOnly ctx T.emit _ s (by decide),legacy]
  cases kind <;>
    simp only [IntegerLoad.term,IntegerLoad.tag,IntegerLoad.ruleId] at * <;>
    cases hp <;>
    isel_eval [*,IntegerLoad.term,IntegerLoad.tag,IntegerLoad.ruleId,
      rule_inst_3576,rule_inst_3583,rule_inst_3590,rule_inst_3597,
      rule_inst_3605,rule_inst_3612,rule_inst_3620,
      sem_ctor,sem_mkData,sem_i64,temp,reg,emit]

/-- Every integer store helper produces its exact side-effect payload and trace.
The enclosing root emits this payload. The helper leaves the complete state unchanged. -/
theorem integer_store_forward (kind : IntegerStore) {p : Program} (hp : Data p)
    (ctx : Ctx) {cfg : Config} (overlap : cfg.checkOverlap = false)
    (st : State) (trace : Array RuleId) (fuel : Nat) (address flags value : V) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+10) 46 kind.term
      [address,flags,value]).run (st,trace) =
      .ok (some (.data 46 0 [.data 58 kind.tag [value,address,flags]]),
        st,trace.push kind.ruleId) := by
  cases kind <;> cases hp <;>
    isel_eval [*,IntegerStore.term,IntegerStore.tag,IntegerStore.ruleId,
      rule_inst_3660,rule_inst_3666,rule_inst_3672,rule_inst_3678,
      sem_ctor,sem_mkData]

end Backend.Stock.Proof.MemoryHelpers

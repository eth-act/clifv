import FV.Backend.Proof.StockAlu
import FV.Backend.Proof.IselMemHelpers

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem stock_sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem stock_sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem stock_sem_i64 (ctx : Ctx) :
    (Stock.sem ctx).prim 14 "I64" = some (.ty (.int 64)) := rfl

/-- The real load helper allocates a fresh mapped destination and emits the
decoded load, retaining Stock scheduling fields and the actual rule trace. -/
theorem stock_uload32_helper {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (st : State) (tr : Array RuleId) (n : Nat)
    (amv flv : V) (m : MInst)
    (decoded : MInst.ofV (.data 58 14 [.reg (st.base.fresh .int).1,amv,flv]) = some m) :
    (applyTerm p (Stock.sem ctx) cfg (n + 20) 27 533 [amv,flv]).run (st,tr) =
      .ok (some (.reg (st.base.fresh .int).1),
        {st with base := (st.base.fresh .int).2.emit m},tr.push rule_inst_3605.id) := by
  have temp (s : State) : Stock.externCtor ctx T.temp_writable_reg [.ty (.int 64)] s =
      .ok (.reg (s.base.fresh .int).1,{s with base := (s.base.fresh .int).2}) := rfl
  have reg (r : Reg) (s : State) : Stock.externCtor ctx T.writable_reg_to_reg [.reg r] s =
      .ok (.reg r,s) := rfl
  have emit (s : State) : Stock.externCtor ctx T.emit
      [.data 58 14 [.reg (st.base.fresh .int).1,amv,flv]] s =
        .ok (.op .unit,{s with base := s.base.emit m}) := by
    have legacy : Backend.externCtor ctx T.emit
        [.data 58 14 [.reg (st.base.fresh .int).1,amv,flv]] s.base =
          .ok (.op .unit,s.base.emit m) := by
      change (match MInst.ofV (.data 58 14 [.reg (st.base.fresh .int).1,amv,flv]) with
        | some i => ExtResult.ok (V.op .unit,s.base.emit i) | none => _) = _
      rw [decoded]
    rw [stock_ctor_baseOnly ctx T.emit _ s (by decide),legacy]
  cases hp
  isel_eval [*,rule_inst_3605,stock_sem_ctor,stock_sem_mkData,stock_sem_i64,
    temp,reg,emit]

end Backend.Stock.Memory

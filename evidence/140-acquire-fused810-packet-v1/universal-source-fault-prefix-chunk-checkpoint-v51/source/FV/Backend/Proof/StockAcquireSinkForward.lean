import FV.Backend.Proof.StockAcquireForward
import FV.Backend.Proof.StockPatternSink

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The real atomic sink helper retains its producer and demands its original address.
The selected root must supply both actual constructor receipts internally. -/
theorem sink_atomic_forward {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {ii pointer : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (installed : ctx.insts[ii]? = some info)
    (atomic : info.data = .data 152 17 [.data 151 158 [],.value pointer,.op (.memFlags flags)])
    {st sunk next : State} {address : Reg}
    (sink : Stock.externCtor ctx T.sink_inst [.inst ii] st = .ok (.op .unit,sunk))
    (demand : Stock.externCtor ctx T.put_in_reg [.value pointer] sunk = .ok (.reg address,next))
    (trace : Array RuleId) (fuel : Nat) :
    (applyTerm p (Stock.sem ctx) cfg (fuel+30) 27 564 [.inst ii]).run (st,trace) =
      .ok (some (.reg address),next,trace.push rule_inst_3905.id) := by
  have extract (s : State) : (Stock.sem ctx).extract T.inst_data_value (.inst ii) s =
      .ok [.ty (info.resTys.head?.getD .invalid),info.data] := by
    change (match ctx.insts[ii]? with
      | some found => ExtResult.ok [V.ty (found.resTys.head?.getD .invalid),found.data]
      | none => ExtResult.unmodeled s!"inst {ii}") = _
    rw [installed]
  have ctor (term : Term) (args : List V) (s : State) :
    (Stock.sem ctx).ctor term args s = Stock.externCtor ctx term args s := rfl
  have unData (ty : Nat) (value : V) : (Stock.sem ctx).unData ty value = (Backend.sem ctx).unData ty value := rfl
  cases hp
  isel_eval [*,rule_inst_3905,extract,ctor,unData,Backend.sem]

end Backend.Stock.Proof.AcquireHelpers

import FV.Backend.Proof.StockAcquirePendingRequestGuard
import FV.Backend.Proof.StockAcquirePairedReadFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Successful real register requests recover their binding from the full pending history.
The enclosing family proof must derive source availability and the actual sink-frame equality internally. -/
theorem stock_lower_requested_pending_value_held {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} {frontier : ReadEffectFrontier event.ctx env program}
    {state requestBefore requestAfter : State} {value : Nat} {reg : Reg}
    (requested : Stock.externCtor event.ctx T.put_in_reg [.value value] requestBefore = .ok (.reg reg,requestAfter))
    (sunkFrame : requestBefore.sunk = state.sunk)
    (retained : ∀ captured ∈ frontier.history,captured.record ∈ event.output.records)
    (marked : PendingReadMarks frontier state) (retired : RetiredUndemanded frontier state)
    {available : Nat → Prop} {frame : Clif.Frame} {regs : Nat → CV}
    (held : PendingValuesHeld frontier.history (fun x => Demanded state x ∧ available x) frame regs)
    (required : Demanded state value ∧ available value) : ValueHeld event.ctx frame regs value := by
  have pending := frontier_pending_values held retired
  have pendingRetained : ∀ captured ∈ frontier.pending,captured.record ∈ event.output.records := by
    intro captured member
    apply retained captured
    rw [frontier.split]
    exact List.mem_append_right _ member
  have allowed : DemandAllowed event.ctx state value := by
    intro producer defined
    rw [← sunkFrame]
    exact put_in_reg_demand_allowed requested producer defined
  have notSuspended := stock_lower_allowed_not_suspended run scope dominated events pendingRetained marked allowed
  exact pending value required notSuspended

end Backend.Stock.Proof.Acquire810

import FV.Backend.Proof.StockEntrySeed

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual retained context preserves the entire proof-selected entry file. -/
theorem stock_lower_event_entry_seed {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) (fr : Clif.Frame) :
    entrySeed event.ctx fr = entrySeed result.ctx fr := by
  classical
  let make (lookup : Nat → Option Reg) (key : Nat) : CV :=
    if h : ∃ pair : Nat × Clif.Val,
        lookup pair.1 = some (.vreg key .int) ∧ fr.regs pair.1 = some pair.2 then
      (Classical.choose h).2.bits.setWidth 128
    else 0
  change make event.ctx.valueReg? = make result.ctx.valueReg?
  rw [funext (stock_lower_record_context run scope events).2.1]

end Backend.Stock.Proof

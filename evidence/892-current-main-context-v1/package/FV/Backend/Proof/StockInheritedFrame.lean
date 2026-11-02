import FV.Backend.Proof.StockInheritedValues

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The existing rule's outside-interval frame is sufficient for carry; its
instruction semantics and write bounds need not be reproved by the CFG layer. -/
theorem record_frame_carry {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {record : ScanRecord}
    (records : record ∈ event.output.records) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (step : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm'))
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) event.block 0)
    {ρ ρ' : Nat → CV}
    (kept : ∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = ρ k)
    (held : ValuesHeld needed event.ctx fr (fun k => ρ (aliasNum result.final.alias k))) :
    ValuesHeld needed event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  have sourceFrame := source_entry_carry run events split statement current step available
  have maps := (stock_lower_record_context run scope events).2.1
  intro x member value read
  rw [sourceFrame x member] at read
  obtain ⟨key,mapped,old⟩ := held x member value read
  have outside := stock_lower_available_alias_outside_record run scope dominated events records
    split.block statement current (availOf_mono (Nat.zero_le j) (available x member))
    (by rw [← maps]; exact mapped)
  refine ⟨key,mapped,?_⟩
  change VHolds value (ρ' (aliasNum result.final.alias key))
  rw [kept _ outside]
  exact old

end Backend.Stock.Proof.Inherited

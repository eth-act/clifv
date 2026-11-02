import FV.Backend.Proof.StockRecordIntervals
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- Already-held original values survive an internal fresh fragment when their
resolved source registers lie outside the enclosing record allocation interval. -/
theorem stock_div_held_interval_transfer {ctx : Ctx} {fr : Clif.Frame} {needed : Nat → Prop}
    {aliases : Array (Option Nat)} {ρ ρ' : Nat → CV} {lo hi first last : Nat}
    (held : ValuesHeld needed ctx fr (fun k => ρ (aliasNum aliases k)))
    (bounds : lo ≤ first ∧ last ≤ hi)
    (outside : ∀ x key,needed x → ctx.valueReg? x = some (.vreg key .int) →
      (fr.regs x).isSome = true → aliasNum aliases key < lo ∨ hi ≤ aliasNum aliases key)
    (kept : ∀ k,k < first ∨ last ≤ k → ρ' k = ρ k) :
    ValuesHeld needed ctx fr (fun k => ρ' (aliasNum aliases k)) := by
  intro x required value lookup
  obtain ⟨key,mapped,input⟩ := held x required value lookup
  refine ⟨key,mapped,?_⟩
  have interval := outside x key required mapped (by rw [lookup]; rfl)
  change VHolds value (ρ' (aliasNum aliases key))
  rw [kept _ (by omega)]
  exact input
/-- Original source availability in a successful actual driver supplies the
noncapture facts used by composition. These are derived from records, not added
to the original source input conditions. -/
theorem stock_div_available_record_outside {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {block : Clif.Block} {stmt : Clif.Stmt}
    (foundBlock : f.blocks[bi]? = some block) (foundStmt : block.body[j]? = some stmt)
    (current : record.inst = blockStart f bi + j) {fr : Clif.Frame}
    (maps : ∀ x,event.ctx.valueReg? x = result.ctx.valueReg? x) :
    ∀ x key,event.ctx.valueReg? x = some (.vreg key .int) →
      ((restrict fr (availOf f (availIn f result.ctx) bi j)).regs x).isSome = true →
      aliasNum result.final.alias key < record.input.base.nextVreg ∨
        record.output.state.base.nextVreg ≤ aliasNum result.final.alias key := by
  intro x key mapped present
  have available := restrict_regs_isSome present
  have originalMap : result.ctx.valueReg? x = some (.vreg key .int) := by
    rw [← maps x]; exact mapped
  exact stock_lower_available_alias_outside_record run scope dominated events records
    foundBlock foundStmt current available originalMap
end Backend.Stock.Proof.ScalarDiv

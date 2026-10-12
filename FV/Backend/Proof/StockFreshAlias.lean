import FV.Backend.Proof.StockRecordedFlow
import FV.Backend.Proof.StockDriverBounds

/-! Fresh targets of actual Stock lowering are terminal in its final alias map.
These facts discharge the fresh alternative of final recorded alias origins;
source-register chains and reserved-value semantics remain separate obligations. -/
namespace Backend.Stock.Proof
open Backend.Proof.Driver

/-- The real driver's final resolver leaves every fresh register unchanged.
The alias-domain bound comes from successful lowering, not a new program premise. -/
theorem stock_lower_freshAlias_terminal {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {n : Nat}
    (fresh : result.initial.base.nextVreg ≤ n) :
    (result.final.alias[n]?).join = none ∧ aliasNum result.final.alias n = n := by
  have outside : result.final.alias.size ≤ n :=
    Nat.le_trans (stock_lower_allocationBounds run).1 fresh
  have absent : (result.final.alias[n]?).join = none := by
    rw [Array.getElem?_eq_none outside]
    rfl
  exact ⟨absent, chaseF_none absent _⟩

/-- Inhabited by the actual nonempty emitted-call driver witness already used
for final alias origins; no new native certificate is introduced. -/
theorem stock_lower_freshAlias_terminal_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent)
      (record : ScanRecord) (step : Step),
      Stock.lower f = .ok result ∧ f.blocks.length ≠ 0 ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (result.final.alias[result.initial.base.nextVreg]?).join = none ∧
      aliasNum result.final.alias result.initial.base.nextVreg = result.initial.base.nextVreg := by
  obtain ⟨result, event, record, step, target, scope, dominated, nonempty, run,
    events, records, index, recorded, emitted, rest⟩ :=
    stock_lower_emitted_record_finalAliasOrigins_noInherited_witness
  refine ⟨_, result, event, record, step, run, nonempty, events, records, recorded, emitted, ?_⟩
  exact stock_lower_freshAlias_terminal run (Nat.le_refl _)

end Backend.Stock.Proof

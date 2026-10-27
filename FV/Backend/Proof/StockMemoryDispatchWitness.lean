import FV.Backend.Proof.StockMemoryRecordFrame
import FV.Backend.Proof.StockMemoryRecordWitness

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The complete real lowering inhabits automatic original-source dispatch. -/
theorem source_dispatch_witness : ∃ input : RecordInput,
    input.step.rules.getLast? = some rule_lower_2610.id := by
  obtain ⟨input⟩ := record_input
  exact ⟨input,stock_lower_load_i32_selected_id input.run scope input.events input.records
    input.source input.clif input.recorded input.emitted⟩

/-- The same nonempty-heap original lowering inhabits full load-record framing. -/
theorem load_sunk_frame_witness : ∃ input : RecordInput,
    input.record.output.state.sunk = input.record.input.sunk := by
  obtain ⟨input⟩ := record_input
  exact ⟨input,stock_lower_parameter_load_sunk_eq input.run scope input.events input.records
    input.source input.clif input.parameter input.pointer input.recorded input.emitted⟩

end Backend.Stock.Memory.LoadFixture

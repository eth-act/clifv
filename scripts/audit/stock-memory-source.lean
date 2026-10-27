import FV.Backend.Proof.StockMemoryContractWitness
import FV.Backend.Proof.StockMemoryLoadWitness
import FV.Backend.Proof.StockMemoryGuardedWitness
import FV.Backend.Proof.StockMemoryOrdinaryWitness
import FV.Backend.Proof.StockMemoryReturnWitness
import FV.Backend.Proof.StockMemoryEntryWitness

#print axioms Backend.Stock.Memory.domain_of_scalar
#print axioms Backend.Stock.Memory.existing_source_witness
#print axioms Backend.Stock.Memory.load_source_result
#print axioms Backend.Stock.Memory.mapped_unscaled_address
#print axioms Backend.Stock.Memory.mapped_unscaled_load
#print axioms Backend.Stock.Memory.LoadFixture.source_load
#print axioms Backend.Stock.Memory.LoadFixture.memory_world
#print axioms Backend.Stock.Memory.LoadFixture.load_source_result_witness
#print axioms Backend.Stock.Memory.LoadFixture.mapped_load_witness
#print axioms Backend.Stock.Memory.stock_uload32_helper
#print axioms Backend.Stock.Memory.LoadFixture.selected_load_helper_witness
#print axioms Backend.Stock.Memory.load_source_seqRun
#print axioms Backend.Stock.Memory.mapped_unsigned_address
#print axioms Backend.Stock.Memory.stock_parameter_amode_zero
#print axioms Backend.Stock.Memory.stock_parameter_load_address
#print axioms Backend.Stock.Memory.stock_parameter_load_rhs
#print axioms Backend.Stock.Memory.LoadFixture.unsigned_load_witness
#print axioms Backend.Stock.Memory.LoadFixture.selected_load_rhs_witness
#print axioms Backend.Stock.Memory.LoadFixture.selected_load_address_witness
#print axioms Backend.Stock.Memory.stock_lower_parameter_load_record
#print axioms Backend.Stock.Memory.stock_lower_parameter_load_values
#print axioms Backend.Stock.Memory.LoadFixture.scope
#print axioms Backend.Stock.Memory.LoadFixture.dominated
#print axioms Backend.Stock.Memory.LoadFixture.record_observed
#print axioms Backend.Stock.Memory.LoadFixture.record_input
#print axioms Backend.Stock.Memory.LoadFixture.actual_load_record_witness
#print axioms Backend.Stock.Memory.LoadFixture.guarded_load_source_witness
#print axioms Backend.Stock.Memory.stock_match_load_i32
#print axioms Backend.Stock.Memory.stock_lower_load_selected_receipts
#print axioms Backend.Stock.Memory.stock_lower_load_selected_values
#print axioms Backend.Stock.Memory.LoadFixture.RecordInput.selected
#print axioms Backend.Stock.Memory.LoadFixture.selected_receipts_witness
#print axioms Backend.Stock.Memory.stock_lower_parameter_load_record_full
#print axioms Backend.Stock.Memory.stock_lower_load_operand_coverage
#print axioms Backend.Stock.Memory.stock_lower_load_source_step
#print axioms Backend.Stock.Memory.stock_lower_load_scan_fall_refines
#print axioms Backend.Stock.Memory.LoadFixture.guarded_load_scan_witness

#print axioms Backend.Stock.Proof.OrdinaryBody.actual_ordinary_source_step
#print axioms Backend.Stock.Proof.OrdinaryBody.actual_ordinary_source_execution_frame
#print axioms Backend.Stock.Memory.LoadFixture.RecordInput.atBlock
#print axioms Backend.Stock.Memory.LoadFixture.RecordInput.body_split
#print axioms Backend.Stock.Memory.LoadFixture.RecordInput.body_record
#print axioms Backend.Stock.Memory.LoadFixture.RecordInput.body_records
#print axioms Backend.Stock.Memory.LoadFixture.ordinary_load_step_witness
#print axioms Backend.Stock.Memory.LoadFixture.ordinary_load_body_execution_witness
#print axioms Backend.Stock.Proof.OrdinaryBody.actual_ordinary_return_refines_at
#print axioms Backend.Stock.Proof.OrdinaryBody.actual_ordinary_entry_return_refines_frame
#print axioms Backend.Stock.Memory.EntryFixture.ordinary_entry_return_witness
#print axioms Backend.Stock.Memory.LoadFixture.actual_load_return_block_witness

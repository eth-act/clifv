import FV.Backend.Proof.StockMemoryContractWitness
import FV.Backend.Proof.StockMemoryLoadWitness
import FV.Backend.Proof.StockMemoryGuardedWitness
import FV.Backend.Proof.StockMemoryOrdinaryWitness
import FV.Backend.Proof.StockMemoryReturnWitness
import FV.Backend.Proof.StockMemoryEntryWitness
import FV.Backend.Proof.StockMemoryDispatchWitness
import FV.Backend.Proof.StockMemorySingleWitness
import FV.Backend.Proof.StockMemoryReadWitness
import FV.E2E.StockMemoryReadWitness

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

#print axioms Backend.Stock.Memory.stock_selected_load_i32_rule
#print axioms Backend.Stock.Memory.stock_lower_load_i32_selected_id
#print axioms Backend.Stock.Memory.stock_lower_load_source_step_auto
#print axioms Backend.Stock.Memory.stock_lower_load_scan_fall_refines_auto
#print axioms Backend.Stock.Memory.stock_lower_parameter_load_sunk_eq
#print axioms Backend.Stock.Memory.LoadFixture.source_dispatch_witness
#print axioms Backend.Stock.Memory.LoadFixture.load_sunk_frame_witness

#print axioms Backend.Stock.Proof.stock_lower_returned_definition_emitted
#print axioms Backend.Stock.Memory.stock_single_load_return_body
#print axioms Backend.Stock.Proof.OrdinaryBody.ordinary_source_notrap
#print axioms Backend.Stock.Memory.domain_of_single_load_return
#print axioms Backend.Stock.Memory.SingleFixture.scope
#print axioms Backend.Stock.Memory.SingleFixture.dominated
#print axioms Backend.Stock.Memory.SingleFixture.lowered
#print axioms Backend.Stock.Memory.SingleFixture.domain
#print axioms Backend.Stock.Memory.SingleFixture.complete_load_function_witness

#print axioms Backend.Stock.Memory.initialized_load_value_eq
#print axioms Backend.Stock.Memory.load_source_result_pair
#print axioms Backend.Stock.Memory.load_source_result_pairR
#print axioms Backend.Stock.Memory.stock_lower_load_paired_record
#print axioms Backend.Stock.Memory.LoadFixture.paired_load_read_witness
#print axioms E2E.StockMemoryReadWitness.guarded_paired_load_witness
#print axioms E2E.StockMemoryReadWitness.guarded_actual_record_pair_witness

#print axioms E2E.StockMemory.stock_lower_load_paired_source_step
#print axioms E2E.StockMemory.stock_lower_load_scan_pair
#print axioms E2E.StockMemory.stock_lower_load_paired_scan
#print axioms E2E.StockMemoryReadWitness.guarded_actual_source_scan_pair_witness
#print axioms E2E.StockMemoryReadWitness.pairsem_scan_interface_witness

import FV.Backend.Proof.StockAcquireRecordWitness
import FV.Backend.Proof.StockAcquireVirtualReturn
import FV.Backend.Proof.StockAcquireEntryNormal
import FV.Backend.Proof.StockAcquireTrapBoundary
import FV.Backend.Proof.StockAcquireSourceReturn
import FV.Backend.Proof.StockAcquireSourceDomain
import FV.Backend.Proof.StockAcquire810Witness
import FV.Backend.Proof.StockAcquireHelpers
import FV.Backend.Proof.StockAcquireValue
import FV.Backend.Proof.StockAcquireForward
import FV.Backend.Proof.StockAcquireBinding
import FV.Backend.Proof.StockAcquireSourceOutcome
import FV.Backend.Proof.StockAcquireEntry

#print axioms Backend.Stock.Proof.Acquire810.original_scope_selects810
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_helpers_project_and_preserve
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_helper_success
#print axioms Backend.Stock.Proof.AcquireHelpers.stock_acquire_call
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_widened_value
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_forward
#print axioms Backend.Stock.Proof.Acquire810.acquire_result_binding
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_pair_run
#print axioms Backend.Stock.Proof.Acquire810.source_three_steps
#print axioms Backend.Stock.Proof.Acquire810.source_more_steps
#print axioms Backend.Stock.Proof.Acquire810.source_first_trap
#print axioms Backend.Stock.Proof.Acquire810.original_source_entry
#print axioms Backend.Stock.Proof.Acquire810.first_source_memory_trap

#print axioms Backend.Stock.Proof.Acquire810.actual_record_binding
#print axioms Backend.Stock.Proof.Acquire810.lowered_byte_return
#print axioms Backend.Stock.Proof.Acquire810.original_entry_normal_form
#print axioms Backend.Stock.Proof.Acquire810.lowered_args_prefix
#print axioms Backend.Stock.Proof.Acquire810.lowered_byte_access_fault
#print axioms Backend.Stock.Proof.Acquire810.source_returned_read
#print axioms Backend.Stock.Proof.Acquire810.entry_returned_read
#print axioms Backend.Stock.Proof.Acquire810.original_returns
#print axioms Backend.Stock.Proof.Acquire810.original_traps

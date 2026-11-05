import FV.Backend.Proof.StockAcquire810Witness
import FV.Backend.Proof.StockAcquireAllocated
import FV.Backend.Proof.StockAcquireAllocatedLine
import FV.Backend.Proof.StockAcquireArmFault
import FV.Backend.Proof.StockAcquireBinding
import FV.Backend.Proof.StockAcquireCompiledCoverage
import FV.Backend.Proof.StockAcquireCompiledWitness
import FV.Backend.Proof.StockAcquireEncodingFault
import FV.Backend.Proof.StockAcquireEntry
import FV.Backend.Proof.StockAcquireEntryNormal
import FV.Backend.Proof.StockAcquireFaultSite
import FV.Backend.Proof.StockAcquireForward
import FV.Backend.Proof.StockAcquireHalt
import FV.Backend.Proof.StockAcquireHelpers
import FV.Backend.Proof.StockAcquireLineFault
import FV.Backend.Proof.StockAcquireMachine
import FV.Backend.Proof.StockAcquireMachineBoundary
import FV.Backend.Proof.StockAcquireMachineCheck
import FV.Backend.Proof.StockAcquireOriginal
import FV.Backend.Proof.StockAcquirePrepare
import FV.Backend.Proof.StockAcquirePreparedShapes
import FV.Backend.Proof.StockAcquireRealizes
import FV.Backend.Proof.StockAcquireRecordWitness
import FV.Backend.Proof.StockAcquireRegisterLevel
import FV.Backend.Proof.StockAcquireShapeCheck
import FV.Backend.Proof.StockAcquireSourceDomain
import FV.Backend.Proof.StockAcquireSourceMachine
import FV.Backend.Proof.StockAcquireSourceOutcome
import FV.Backend.Proof.StockAcquireSourceReturn
import FV.Backend.Proof.StockAcquireStage
import FV.Backend.Proof.StockAcquireTrace
import FV.Backend.Proof.StockAcquireTrapBoundary
import FV.Backend.Proof.StockAcquireValue
import FV.Backend.Proof.StockAcquireVirtualReturn

#print axioms Backend.Stock.Proof.Acquire810.original_scope_selects810 -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_allocated_boundary
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_line
#print axioms Backend.Stock.Proof.Acquire810.instFaults_acquire_byte
#print axioms Backend.Stock.Proof.Acquire810.acquire_result_binding
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_pair_run
#print axioms Backend.Stock.Proof.Acquire810.acquire_compile_sound
#print axioms Backend.Stock.Proof.Acquire810.acquire_complete_covered_compilation -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_complete_compilation -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_encoding
#print axioms Backend.Stock.Proof.Acquire810.encoded_acquire_byte_fault
#print axioms Backend.Stock.Proof.Acquire810.encoded_acquire_byte_fault_step
#print axioms Backend.Stock.Proof.Acquire810.original_source_entry
#print axioms Backend.Stock.Proof.Acquire810.first_source_memory_trap
#print axioms Backend.Stock.Proof.Acquire810.original_entry_normal_form
#print axioms Backend.Stock.Proof.Acquire810.AcquireAt.load_inv
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_fault_site
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_forward
#print axioms Backend.Stock.Proof.Acquire810.VAcquireTrapFrom.boundary
#print axioms Backend.Stock.Proof.Acquire810.star_haltAcquire
#print axioms Backend.Stock.Proof.Acquire810.acquireTrap_halt
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_helpers_project_and_preserve
#print axioms Backend.Stock.Proof.AcquireHelpers.acquire_helper_success
#print axioms Backend.Stock.Proof.AcquireHelpers.stock_acquire_call
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_line_fault
#print axioms Backend.Stock.Proof.Acquire810.regLevel_acquire_fault_world_value
#print axioms Backend.Stock.Proof.Acquire810.regLevel_acquire_fault_boundary_world_value
#print axioms Backend.Stock.Proof.Acquire810.regLevel_acquire_fault_boundary_worldX_value
#print axioms Backend.Stock.Proof.Acquire810.acquire_no_i128 -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_legalize_identity -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_original_complete_compilation -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquireTraps_clean
#print axioms Backend.Stock.Proof.Acquire810.acquireTraps_prune
#print axioms Backend.Stock.Proof.Acquire810.acquireTraps_prepare
#print axioms Backend.Stock.Proof.Acquire810.prepared_acquire_shapes -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.realizes_haltAcquire
#print axioms Backend.Stock.Proof.Acquire810.actual_record_binding -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_register_level_boundary
#print axioms Backend.Stock.Proof.Acquire810.acquireByteShape_of_check
#print axioms Backend.Stock.Proof.Acquire810.original_returns -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.original_traps -- witness: native_decide
#print axioms E2E.backend_correct_worldX_stock_acquire810 -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.source_three_steps
#print axioms Backend.Stock.Proof.Acquire810.source_more_steps
#print axioms Backend.Stock.Proof.Acquire810.source_first_trap
#print axioms Backend.Stock.Proof.Acquire810.source_returned_read
#print axioms Backend.Stock.Proof.Acquire810.entry_returned_read
#print axioms Backend.Stock.Proof.Acquire810.acquireTrap_stage
#print axioms Backend.Stock.Proof.Acquire810.acquireTrap_gotV_value
#print axioms Backend.Stock.Proof.Acquire810.realizes_haltAcquire_trace
#print axioms Backend.Stock.Proof.Acquire810.acquire_allocated_boundary_trace
#print axioms Backend.Stock.Proof.Acquire810.acquire_register_level_boundary_from_trace
#print axioms Backend.Stock.Proof.Acquire810.lowered_args_prefix -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.lowered_byte_access_fault -- witness: native_decide
#print axioms Backend.Stock.Proof.Acquire810.acquire_byte_widened_value
#print axioms Backend.Stock.Proof.Acquire810.lowered_byte_return -- witness: native_decide

import FV.E2E.StockCallStoreFaultMachine
import FV.E2E.StockCallStorePreparedShapes
import FV.E2E.StockCallStoreProviderWitness
import FV.Backend.Proof.StockCallStoreCalleeTrap
import FV.E2E.StockCallStoreNI
import FV.E2E.StockCallStoreCompiledWitness
import FV.Backend.Proof.StockCallStoreFault
import FV.E2E.StockCallStoreSourceWitness
#print axioms Backend.Stock.Proof.CallStoreResult.call_then_store_of_source
#print axioms Backend.Stock.Proof.CallStoreResult.source_pointer
#print axioms Backend.Stock.Proof.CallStoreResult.source_store_returns
#print axioms Backend.Stock.Proof.CallStoreResult.source_store_faults
#print axioms Backend.Stock.Proof.CallStoreResult.source_call_fault_or_continues
#print axioms Backend.Stock.Proof.CallStoreResult.call_then_store_access
#print axioms Backend.Stock.Proof.CallStoreResult.source_fault_decomposition
#print axioms E2E.CallStoreSourceWitness.default_store_fault
#print axioms E2E.CallStoreSourceWitness.store_reached
#print axioms E2E.CallStoreSourceWitness.store_fault_at
#print axioms E2E.CallStoreSourceWitness.default_store_return
#print axioms E2E.CallStoreFixture.original_source_exact -- witness: native_decide
#print axioms E2E.CallStoreFixture.actual_retained_and_saved -- witness: native_decide
#print axioms Backend.Stock.CallStore.Layout.source_fields
#print axioms Backend.Stock.CallStore.Layout.scan_fields
#print axioms Backend.Stock.CallStore.check_sound
#print axioms Backend.Stock.CallStore.prelude_read_checks
#print axioms Backend.Stock.CallStore.Layout.pointer_type
#print axioms Backend.Stock.CallStore.Layout.source_result
#print axioms Backend.Stock.Proof.CallStoreResult.pointer_address
#print axioms Backend.Stock.CallStore.execute_tail
#print axioms Backend.Stock.CallStore.Layout.return_function_for
#print axioms Backend.Stock.CallStore.Layout.return_function
#print axioms Backend.Stock.CallStore.no_trap_under_original_condition
#print axioms Backend.Stock.CallStore.check_return_store_domain
#print axioms Backend.Stock.CallStore.Layout.ready
#print axioms Backend.Stock.CallStore.Ready.virtual_return
#print axioms Backend.Stock.CallStore.Ready.execute
#print axioms Backend.Stock.CallStore.Ready.execute_other
#print axioms E2E.backend_correct_world_niX_stock_call_store_return
#print axioms E2E.CallStoreCompiledWitness.complete_caller -- witness: native_decide
#print axioms Backend.Stock.CallStore.access_tail
#print axioms Backend.Stock.CallStore.Layout.source_fault
#print axioms Backend.Stock.CallStore.Layout.fault_ready
#print axioms Backend.Stock.CallStore.FaultReady.execute
#print axioms E2E.backend_store_fault_or_callee_stock_call_store
#print axioms Backend.Stock.CallStore.lowerWithPrevious_retry
#print axioms Backend.Stock.CallStore.lowerWithPrevious_selects
#print axioms Backend.Stock.CallStore.candidate_stock
#print axioms Backend.Stock.CallStore.lowerWithPrevious_preserves
#print axioms Backend.Stock.CallStore.lowerWithPrevious_accepts
#print axioms Backend.Stock.Proof.CallStoreResult.source_callee_trap
#print axioms E2E.CallStoreCompiledWitness.checked_caller -- witness: native_decide
#print axioms E2E.CallStoreProviderWitness.actual_provider -- witness: native_decide
#print axioms E2E.CallStoreCompiledWitness.prepared_access_shapes -- witness: native_decide

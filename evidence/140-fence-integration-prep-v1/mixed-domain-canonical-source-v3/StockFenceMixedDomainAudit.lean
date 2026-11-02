import FV.Backend.Proof.StockFenceAccessComposition
import FV.Backend.Proof.StockFenceAccessWitness
import FV.Backend.Proof.StockFenceBodyFacts
import FV.Backend.Proof.StockFenceMixedBodyRefines
import FV.Backend.Proof.StockFenceMixedBodyTrap
import FV.Backend.Proof.StockFenceMixedDomain
import FV.Backend.Proof.StockFenceMixedNonvacuity
import FV.Backend.Proof.StockFenceRetainedWitness
import FV.Backend.Proof.StockMemoryAccessEntryTrap
import FV.Backend.Proof.StockMemoryAccessPlacement
import FV.Backend.Proof.StockMemoryAccessReach
import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockMemoryAccessSourcePrefix
import FV.Backend.Proof.StockMemoryAccessSourceTrap
import FV.Backend.Proof.StockMemoryAccessStoreEmission
import FV.Backend.Proof.StockMemoryAccessTrap
import FV.Backend.Proof.StockMemoryDivAccessRefines
import FV.Backend.Proof.StockMemoryFaultContract
import FV.Backend.Proof.StockMemoryLoadAccessTrap
import FV.Backend.Proof.StockMemoryOffsetSixteenAddress
import FV.Backend.Proof.StockMemoryOffsetSixteenLoad
import FV.Backend.Proof.StockMemoryOffsetSixteenLoadRecord
import FV.Backend.Proof.StockMemoryOffsetSixteenScanRefines
import FV.Backend.Proof.StockMemoryOffsetSixteenSourceValues
import FV.Backend.Proof.StockMemoryOffsetSixteenValues
import FV.Backend.Proof.StockMemoryStoreAccessTrap

#print axioms Backend.Stock.Proof.MemoryFaults.stock_body_fences_access_first_trap
#print axioms Backend.Stock.Proof.FenceFixture.fault_source_entry
#print axioms Backend.Stock.Proof.FenceFixture.unallocated_first_access_traps
#print axioms Backend.Stock.Proof.FenceFixture.unallocated_first_access_event
#print axioms Backend.Stock.Proof.FenceFixture.mixed_actual_body_facts -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_emitted_result_mapped
#print axioms Backend.Stock.Proof.FenceFixture.mixed_record_fall_refines -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_record_access_trap -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_domain_with_access_traps -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_complete_return -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_complete_division_trap -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_complete_domain_witness -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.FenceFixture.mixed_body_all_emitted -- fixed witness: native_decide
#print axioms Backend.Stock.Proof.MemoryFaults.actual_ordinary_entry_access_trap_refines_frame
#print axioms Backend.Stock.Proof.MemoryFaults.accessTrapRun_at
#print axioms Backend.Stock.Proof.MemoryFaults.trapOrAccessRun_at
#print axioms Backend.Stock.Proof.MemoryFaults.trapOrAccessRun_inbounds
#print axioms Backend.Stock.Proof.MemoryFaults.ordinary_result_next
#print axioms Backend.Stock.Proof.MemoryFaults.ordinary_trap_step
#print axioms Backend.Stock.Proof.MemoryFaults.guarded_with_reach
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_load_memtrap_at
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_load_property
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_store_memtrap_at
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_store_property
#print axioms Backend.Stock.Proof.MemoryFaults.AccessTrapRun.append
#print axioms Backend.Stock.Proof.MemoryFaults.AccessTrapRun.prefix
#print axioms Backend.Stock.Proof.MemoryFaults.TrapOrAccessRun.append
#print axioms Backend.Stock.Proof.MemoryFaults.TrapOrAccessRun.prefix
#print axioms Backend.Stock.Proof.MemoryFaults.scans_access_trap_refines
#print axioms Backend.Stock.Proof.MemoryFaults.actual_ordinary_source_trap_execution
#print axioms Backend.Stock.Proof.MemoryFaults.source_load_trap
#print axioms Backend.Stock.Proof.MemoryFaults.source_store_trap
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_source_load_trap
#print axioms Backend.Stock.Proof.MemoryFaults.indexed_source_store_trap
#print axioms Backend.Stock.Proof.MemoryFaults.stock_lower_store_emission
#print axioms Backend.Stock.Proof.MemoryFaults.VAccessTrapFrom.prefix
#print axioms Backend.Stock.Proof.MemoryFaults.stock_udiv_memory_fall_refines
#print axioms Backend.Stock.Proof.MemoryFaults.stock_udiv_access_first_trap
#print axioms Backend.Stock.Proof.MemoryFaults.domainWithAccessTraps_of_domain
#print axioms Backend.Stock.Proof.MemoryFaults.AccessTrapRun.load
#print axioms Backend.Stock.Proof.MemoryFaults.stock_load_sixteen_access_trap
#print axioms Backend.Stock.Proof.MemoryFaults.stock_load_zero_access_trap
#print axioms Backend.Stock.Memory.IntegerRoots.stock_parameter_amode_sixteen_width
#print axioms Backend.Stock.Memory.IntegerRoots.stock_parameter_load_address_sixteen_width
#print axioms Backend.Stock.Memory.IntegerRoots.stock_parameter_integer_load_sixteen_rhs
#print axioms Backend.Stock.Memory.IntegerRoots.stock_lower_integer_load_sixteen_record
#print axioms Backend.Stock.Memory.IntegerRoots.stock_lower_integer_load_sixteen_scan_fall_refines
#print axioms Backend.Stock.Memory.IntegerRoots.stock_lower_integer_load_sixteen_operand_coverage
#print axioms Backend.Stock.Memory.IntegerRoots.stock_lower_integer_load_sixteen_source_step
#print axioms Backend.Stock.Memory.IntegerRoots.stock_lower_integer_load_sixteen_values
#print axioms Backend.Stock.Proof.MemoryFaults.AccessTrapRun.store
#print axioms Backend.Stock.Proof.MemoryFaults.stock_store_eight_i64_access_trap

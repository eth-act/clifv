import FV.Backend.Proof.StockActualAddSubBodyRefines
import FV.Backend.Lowering.StockScalarAdd
import FV.Backend.Lowering.StockScalarProduction
import FV.Backend.Proof.StockAddSubScanRefines
import FV.Backend.Proof.StockScalarAddChecked
import FV.Backend.Proof.StockScalarAddClass
import FV.Backend.Proof.StockScalarAddCode
import FV.Backend.Proof.StockScalarAddDomain
import FV.Backend.Proof.StockScalarAddSource
import FV.Backend.Proof.StockScalarAddWitness

#print axioms Backend.Stock.Proof.stock_lower_addsub_scan_fall_refines
#print axioms Backend.Stock.Proof.stock_lower_select_addsub_omitted_body_fall_refines
#print axioms Backend.Stock.ScalarAdd.checked_output
#print axioms Backend.Stock.ScalarAdd.eligible_sound
#print axioms Backend.Stock.ScalarAdd.source_eligible
#print axioms Backend.Stock.ScalarAdd.eligible_success_and_edges
#print axioms Backend.Stock.ScalarAdd.eligible_output
#print axioms Backend.Stock.ScalarAdd.eligible_checked_output
#print axioms Backend.Stock.ScalarAdd.outside_class
#print axioms Backend.Stock.ScalarAdd.failed_attempt
#print axioms Backend.Stock.ScalarAdd.d0_outside_class
#print axioms Backend.Stock.ScalarAdd.preserves_d0
#print axioms Backend.Stock.ScalarAdd.preserves_prologue
#print axioms Backend.Stock.ScalarAdd.code_defaultI32
#print axioms Backend.Stock.ScalarAdd.code_systemVI32
#print axioms Backend.Stock.ScalarAdd.code_fastI32
#print axioms Backend.Stock.ScalarAdd.code_defaultI64
#print axioms Backend.Stock.ScalarAdd.code_systemVI64
#print axioms Backend.Stock.ScalarAdd.code_fastI64
#print axioms Backend.Stock.ScalarAdd.code_and_success
#print axioms Backend.Stock.ScalarAdd.context_scope
#print axioms Backend.Stock.ScalarAdd.lowering_domain
#print axioms Backend.Stock.ScalarAdd.Source.source_entry
#print axioms Backend.Stock.ScalarAdd.Source.source_return
#print axioms Backend.Stock.ScalarAdd.Source.source_memory_roundtrip
#print axioms Backend.Stock.ScalarAdd.Source.complete_source_witness
#print axioms Backend.Stock.ScalarAdd.Source.dirty_machine_bits
#print axioms Backend.Stock.ScalarAdd.complete_lowering_source_witness

#print axioms Backend.Stock.Proof.stock_lower_actual_select_addsub_omitted_body_refines

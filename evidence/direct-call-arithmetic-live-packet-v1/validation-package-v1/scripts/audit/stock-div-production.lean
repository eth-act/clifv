import FV.Link.ReachCheckWitness
import FV.E2E.StockDivWitness
import FV.E2E.StockDivSourceWitness
import FV.E2E.SemanticNIBoundary
#print axioms Backend.Stock.Proof.stock_lower_source_result_definition
#print axioms Backend.Stock.Proof.stock_lower_return_demand_unsunk
#print axioms Backend.Stock.Proof.stock_mandatory_unsunk_emitted
#print axioms Backend.Stock.Proof.stock_lower_single_div_return_emitted
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_step
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_execution_frame
#print axioms Backend.Stock.Proof.PureBody.actual_local_return_refines_at
#print axioms Backend.Stock.Proof.PureBody.actual_local_entry_return_refines_frame
#print axioms Backend.Stock.Proof.PureBody.actual_pure_return_refines_at
#print axioms Backend.Stock.Proof.PureBody.actual_pure_entry_return_refines_frame
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_div_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarDiv.stock_lower_div_source_trap
#print axioms Backend.Stock.Proof.stock_lower_div_scan_fall_refines
#print axioms Backend.Stock.Proof.DivBody.actual_single_div_record
#print axioms Backend.Stock.Proof.DivBody.actual_single_div_body_refines
#print axioms Backend.Stock.Proof.DivBody.single_div_source_trap
#print axioms Backend.Stock.Proof.DivBody.trapRun_at
#print axioms Backend.Stock.Proof.DivBody.actual_single_div_entry_return_refines_frame
#print axioms Backend.Stock.Proof.DivBody.actual_single_div_entry_trap_refines_frame
#print axioms Backend.Stock.Scalar.domain_of_single_div
#print axioms Backend.Stock.Scalar.singleDivEligible_sound
#print axioms Backend.Stock.Scalar.sourceOk_sound
#print axioms E2E.DivBoundary.checked_step_frame
#print axioms E2E.DivBoundary.checked_step_transport
#print axioms E2E.DivBoundary.return_transport
#print axioms E2E.DivBoundary.machine_return
#print axioms E2E.DivBoundary.zero_guard_halts
#print axioms E2E.DivBoundary.nonzero_guard_continues
#print axioms E2E.backend_correct_world_niX_stock_div
#print axioms E2E.CompiledSemanticNI.toSemantic
#print axioms E2E.CompiledSemanticNI.of_checks
#print axioms E2E.backend_correct_world_niX_semantic
#print axioms E2E.CompiledSemanticNI.entryRegs
#print axioms E2E.CompiledSemanticNI.noTlsDiv
#print axioms E2E.hasTls_of_vcode_semantic
#print axioms E2E.StockDivNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockDivNIWitness.compiled_exists -- witness: native_decide
#print axioms E2E.StockDivNIWitness.source_entry
#print axioms E2E.StockDivNIWitness.source_runs
#print axioms E2E.StockDivNIWitness.zero_traps
#print axioms E2E.StockDivNIWitness.signed_minimum_overflow
#print axioms E2E.StockDivNIWitness.signed_minimum_remainder

#print axioms Link.LinkSpec.reachOkMap_eq
#print axioms Link.LinkSpec.reachOkMap_empty
#print axioms Link.LinkSpec.reachOkMap_duplicates -- witness: native_decide
#print axioms Link.DeadCleanup.placedPar_eq

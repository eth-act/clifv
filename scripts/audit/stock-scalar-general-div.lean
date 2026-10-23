import FV.Backend.Proof.StockNoLoadSink
import FV.Backend.Proof.StockNoLoadSource
import FV.Backend.Proof.StockNoLoadScan
import FV.Backend.Proof.StockNoLoadDriver
import FV.Backend.Proof.StockScalarDivBodyRecords
import FV.Backend.Proof.StockScalarDivBodyRefines
import FV.Backend.Proof.StockScalarGeneralDivDomain
import FV.Backend.Proof.StockNoLoadDriverWitness
import FV.Backend.Proof.StockNoLoadBranchWitness
import FV.Backend.Proof.StockScalarDivSourceWitness

set_option pp.privateNames true

#print axioms Backend.Stock.Proof.SinkRules.no_load_frames
#print axioms Backend.Stock.Proof.SinkRules.no_load_apply
#print axioms Backend.Stock.Proof.SinkRules.no_load_lower
#print axioms Backend.Stock.Proof.SinkRules.no_load_branch
#print axioms Backend.Stock.Proof.SinkRules.inst_data_no_load
#print axioms Backend.Stock.Proof.SinkRules.build_ctx_no_load
#print axioms Backend.Stock.Proof.SinkRules.scoped_build_ctx_no_load
#print axioms Backend.Stock.Proof.SinkRules.term_ctx_no_load
#print axioms Backend.Stock.Proof.SinkRules.term_data_no_load
#print axioms Backend.Stock.Proof.SinkRules.try_call_data_no_load
#print axioms Backend.Stock.Proof.SinkRules.scalar_div_formats
#print axioms Backend.Stock.Proof.SinkRules.build_ctx_sunk_false
#print axioms Backend.Stock.Proof.SinkRules.scan_no_load_unsunk
#print axioms Backend.Stock.Proof.SinkRules.scan_block_no_load_unsunk
#print axioms Backend.Stock.Proof.SinkRules.scans_no_load_unsunk
#print axioms Backend.Stock.Proof.SinkRules.stock_blockCore_no_load_sunk_eq
#print axioms Backend.Stock.Proof.SinkRules.stock_node_no_load_sunk_eq
#print axioms Backend.Stock.Proof.SinkRules.stock_traversal_no_load_sunk_eq
#print axioms Backend.Stock.Proof.SinkRules.stock_lower_no_load_sunk_eq
#print axioms Backend.Stock.Proof.SinkRules.stock_lower_no_load_unsunk
#print axioms Backend.Stock.Proof.SinkRules.stock_lower_scalar_div_unsunk
#print axioms Backend.Stock.Proof.DivBody.actual_division_record
#print axioms Backend.Stock.Proof.DivBody.actual_scalar_div_families
#print axioms Backend.Stock.Proof.DivBody.actual_scalar_div_body_refines
#print axioms Backend.Stock.Proof.DivBody.actual_scalar_div_entry_return_refines_frame
#print axioms Backend.Stock.Proof.DivBody.actual_scalar_div_entry_trap_refines_frame
#print axioms Backend.Stock.Scalar.domain_of_scalar_div
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_driver_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.BranchWitness.critical_edge_driver_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_domain -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_source_entry -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_source_return -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_source_zero -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_source_overflow -- witness: native_decide
#print axioms Backend.Stock.Proof.SinkRules.DriverWitness.two_division_records -- witness: native_decide

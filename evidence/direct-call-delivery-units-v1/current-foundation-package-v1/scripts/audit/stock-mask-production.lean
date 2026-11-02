import FV.E2E.StockMaskWitness
import FV.E2E.ABIReadMaskSteps
import FV.Backend.Proof.StockZeroResultScan

#print axioms Backend.Stock.Proof.scan_zero_results
#print axioms Backend.Stock.Proof.scan_zero_results_witness
#print axioms Backend.Stock.Proof.stock_lower_bmask_scan_fall_refines
#print axioms Backend.Stock.Proof.MaskBody.family_formats
#print axioms Backend.Stock.Proof.MaskBody.actual_nop_record
#print axioms Backend.Stock.Proof.MaskBody.actual_families
#print axioms Backend.Stock.Proof.MaskBody.Record.fall_refines
#print axioms Backend.Stock.Proof.MaskBody.Record.trap_refines
#print axioms Backend.Stock.Proof.MaskBody.actual_body_refines
#print axioms Backend.Stock.Proof.MaskBody.actual_entry_return_refines_frame
#print axioms Backend.Stock.Proof.MaskBody.actual_entry_trap_refines_frame
#print axioms Backend.Stock.Scalar.domain_of_mask
#print axioms Backend.Stock.Scalar.maskMixedBodyEligible_sound
#print axioms Backend.Stock.Scalar.domain_of_maskEligible
#print axioms Backend.Stock.Scalar.sourceOk_sound
#print axioms Backend.Stock.Scalar.check_sound
#print axioms E2E.MaskRead.no_mem
#print axioms E2E.MaskRead.spec_eq
#print axioms E2E.MaskRead.step_frame
#print axioms E2E.MaskRead.step_frame_witness
#print axioms E2E.StockMaskNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockMaskNIWitness.compiled_cases -- witness: native_decide

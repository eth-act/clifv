import FV.E2E.StockPopcountWitness
import FV.Backend.Proof.StockPopcountZeroWitness
import FV.Backend.Proof.StockPopcountNonzeroWitness

#print axioms Backend.Stock.Proof.PopcountBody.emitted_record_family
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_families
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_body_refines
#print axioms Backend.Stock.Proof.PopcountBody.family_pure
#print axioms Backend.Stock.Proof.PopcountBody.family_quiet
#print axioms Backend.Stock.Proof.PopcountBody.family_single
#print axioms Backend.Stock.Proof.PopcountBody.family_formats
#print axioms Backend.Stock.Proof.PopcountBody.popcount_inst_notrap
#print axioms Backend.Stock.Proof.PopcountBody.popcount_source_notrap
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_entry_return_refines_frame
#print axioms Backend.Stock.Proof.stock_lower_popcount_scan_fall_refines
#print axioms Backend.Stock.Proof.stock_lower_mixed_popcount_record_fall_refines
#print axioms Backend.Stock.Proof.stock_lower_mixed_popcount_body_fall_refines
#print axioms Backend.Stock.Scalar.domain_of_popcount
#print axioms E2E.PopcountRead.step_frame
#print axioms E2E.PopcountRead.no_mem
#print axioms E2E.PopcountRead.spec_eq
#print axioms E2E.StockPopcountNIWitness.checks_true -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.compiled_exists -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.source_entry
#print axioms E2E.StockPopcountNIWitness.source_returns
#print axioms E2E.StockPopcountNIWitness.source_checks_true -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.classifier_accepts -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.selected_roots_present -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.compiled_semantic_exists -- witness: native_decide
#print axioms E2E.StockPopcountNIWitness.source_family
#print axioms Backend.Stock.Scalar.popcountBodyEligible_sound
#print axioms Backend.Stock.Proof.ScalarPopcount.stock_lower_popcount_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarPopcount.ZeroWitness.stock_lower_popcount_source_witness
#print axioms Backend.Stock.Proof.ScalarPopcount.NonzeroWitness.stock_lower_popcount_source_witness

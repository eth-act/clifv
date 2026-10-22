import FV.Backend.Proof.StockPopcountZeroWitness
import FV.Backend.Proof.StockPopcountNonzeroWitness
import FV.E2E.StockPopcountWitness

#print axioms Backend.Stock.Proof.UnchangedHelper.observe
#print axioms Backend.Stock.Proof.stock_match_source_type
#print axioms Backend.Stock.Proof.Popcount.helpers_unchanged
#print axioms Backend.Stock.Proof.Popcount.helpers_closed
#print axioms Backend.Stock.Proof.Popcount.mov_to_fpu_observed
#print axioms Backend.Stock.Proof.Popcount.mov_from_vec_observed
#print axioms Backend.Stock.Proof.Popcount.cnt_observed
#print axioms Backend.Stock.Proof.Popcount.addp_observed
#print axioms Backend.Stock.Proof.Popcount.addv_observed
#print axioms Backend.Stock.Proof.Popcount.opcode_inventory
#print axioms Backend.Stock.Proof.Popcount.source_data
#print axioms Backend.Stock.Proof.Popcount.selected_rule
#print axioms Backend.Stock.Proof.Popcount.rhs_wide_observed
#print axioms Backend.Stock.Proof.Popcount.rhs64_observed
#print axioms Backend.Stock.Proof.Popcount.rhs32_observed
#print axioms Backend.Stock.Proof.Popcount.rhs8_observed
#print axioms Backend.Stock.Proof.Popcount.rhs16_observed
#print axioms Backend.Stock.Proof.Popcount.rhs_observed
#print axioms Backend.Stock.Proof.Popcount.popcount_match
#print axioms Backend.Stock.Proof.Popcount.base_code
#print axioms Backend.Stock.Proof.Popcount.resolved
#print axioms Backend.Stock.Proof.Popcount.selected_values
#print axioms Backend.Stock.Proof.stock_lower_fresh_record_values_of_frame
#print axioms Backend.Stock.Proof.Popcount.available_values
#print axioms Backend.Stock.Proof.Popcount.available_source
#print axioms Backend.Stock.Proof.Popcount.source_by_instruction
#print axioms Backend.Stock.Proof.PopcountBody.family_pure
#print axioms Backend.Stock.Proof.PopcountBody.family_quiet
#print axioms Backend.Stock.Proof.PopcountBody.family_single
#print axioms Backend.Stock.Proof.PopcountBody.family_formats
#print axioms Backend.Stock.Proof.PopcountBody.popcount_inst_notrap
#print axioms Backend.Stock.Proof.PopcountBody.popcount_source_notrap
#print axioms Backend.Stock.Proof.stock_lower_popcount_scan_fall_refines
#print axioms Backend.Stock.Proof.stock_lower_mixed_popcount_record_fall_refines
#print axioms Backend.Stock.Proof.stock_lower_mixed_popcount_body_fall_refines
#print axioms Backend.Stock.Proof.PopcountBody.emitted_record_family
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_families
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_body_refines
#print axioms Backend.Stock.Proof.PopcountBody.actual_popcount_entry_return_refines_frame
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

#print axioms Backend.Stock.Proof.ScalarPopcount.ZeroWitness.stock_lower_popcount_source_witness_scoped
#print axioms Backend.Stock.Proof.ScalarPopcount.NonzeroWitness.stock_lower_popcount_source_witness_scoped

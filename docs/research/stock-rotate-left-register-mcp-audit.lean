import FV.Backend.Proof.StockRotateLeftRegisterWitness
import FV.Backend.Proof.StockRotateSourceValues
import FV.Backend.Proof.StockRotateNarrowRegisterSemantics
import FV.Backend.Proof.StockRotateNarrowRegisterValues
import FV.Backend.Proof.StockRotateNarrowRecordValues
import FV.Backend.Proof.StockRotateNarrowSourceValues
import FV.Backend.Proof.StockRotateWideImmRecordValues
import FV.Backend.Proof.StockRotateWideImmSourceValues
import FV.Backend.Proof.StockRotateNarrowImmRecordValues
import FV.Backend.Proof.StockRotateNarrowImmSourceValues
import FV.Backend.Proof.StockRotateWideSourceValues
import FV.Backend.Proof.StockRotateRegisterRequests
import FV.Backend.Proof.StockRotateMath
import FV.Backend.Proof.StockRotateSemantics
import FV.Backend.Proof.StockRotateRhs
import FV.Backend.Proof.StockRotatePure
import FV.Backend.Proof.StockRotateNarrowRhs
import FV.Backend.Proof.StockRotateNarrowRoots
import FV.Backend.Proof.StockRotateMatch
import FV.Backend.Proof.StockRotateImmediateMatch
import FV.Backend.Proof.StockRotateSelectedValues
import FV.Backend.Proof.StockRotateNarrowValues

#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_neg
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_small_rotate_imm_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_imm_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_rr_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_imm_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_imm_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_pure_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rr_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_helper
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rr_run
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_zext32
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_rhs
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_source_data
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_register_match
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_immediate_match
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_immediate_receipts
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_immediate_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_immediate_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_immediate_requests
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_imm_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_immediate_values

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_pure_sunk

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_wide_register_requests

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_register_requests

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_register_state

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_wide_register_values

#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_register_available_values

#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_register_available_source

#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_narrow_register_resolved
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_register_state
#print axioms Backend.Stock.Proof.ScalarRotate.stock_rotate_selected_narrow_register_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_register_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_register_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_immediate_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_wide_immediate_available_source
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_immediate_available_values
#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_narrow_immediate_available_source

#print axioms Backend.Stock.Proof.ScalarRotate.stock_selected_rotate_rule

#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_source_operands

#print axioms Backend.Stock.Proof.ScalarRotate.stock_lower_rotate_source_by_instruction

#print axioms Backend.Stock.Proof.ScalarRotate.LeftRegisterWitness.stock_lower_rotate_source_witness

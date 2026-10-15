import FV.Backend.Proof.StockAddSubAllSourceValues
import FV.Backend.Proof.StockAddSubAllValues
import FV.Backend.Proof.StockAddSubAuxWitness
import FV.Backend.Proof.StockAddSubDispatch
import FV.Backend.Proof.StockAddSubExtensionWitness
import FV.Backend.Proof.StockAddSubImmediateMatch
import FV.Backend.Proof.StockAddSubImmediateValues
import FV.Backend.Proof.StockAddSubImmediateWitness
import FV.Backend.Proof.StockAddSubMatch
import FV.Backend.Proof.StockAddSubNegativeMatch
import FV.Backend.Proof.StockAddSubNegativePure
import FV.Backend.Proof.StockAddSubNegativeValues
import FV.Backend.Proof.StockAddSubNegativeWitness
import FV.Backend.Proof.StockAddSubObserved
import FV.Backend.Proof.StockAddSubPure
import FV.Backend.Proof.StockAddSubRecordValues
import FV.Backend.Proof.StockAddSubRhs
import FV.Backend.Proof.StockAddSubSelected
import FV.Backend.Proof.StockAddSubSemantics
import FV.Backend.Proof.StockAddSubShiftEdgeWitness
import FV.Backend.Proof.StockAddSubShiftWitness
import FV.Backend.Proof.StockAddSubSourceValues
import FV.Backend.Proof.StockAddSubUnifiedValues
import FV.Backend.Proof.StockAddSubValues
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_available_source
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_source_by_instruction
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_available_values
#print axioms Backend.Stock.Proof.ScalarAddSub.AuxWitness.stock_addsub_negative_projection_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_selected_rule_ids
#print axioms Backend.Stock.Proof.ScalarAddSub.ExtensionWitness.stock_lower_addsub_extension_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.ImmediateWitness.stock_lower_addsub_immediate_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extended_pattern_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_source_data
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match_value
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match_operand
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_match_receipts
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_pure_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_project
#print axioms Backend.Stock.Proof.ScalarAddSub.Negative.stock_addsub_negative_match_project
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.NegativeWitness.stock_lower_addsub_negative_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_observed
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_pure_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_record_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_available_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_reg
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_helper
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_rhs
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_neg_imm_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_first_request
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_requests
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_put_extended_iff
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_requests
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_imm_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_resolved
#print axioms Backend.Stock.Proof.ScalarAddSub.ShiftEdgeWitness.stock_lower_addsub_shift_edge_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.ShiftWitness.stock_lower_addsub_shift_source_witness
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_source_operands
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_available_source
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_lower_addsub_fused_source_from_step
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_fused_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_extend_selected_values
#print axioms Backend.Stock.Proof.ScalarAddSub.stock_addsub_shift_selected_values

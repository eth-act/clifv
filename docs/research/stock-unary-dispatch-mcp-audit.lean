import FV.Backend.Proof.StockRootOpcode
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockUnaryDispatch
import FV.Backend.Proof.StockNegDispatchWitness
import FV.Backend.Proof.StockBitrevDispatchWitness
import FV.Backend.Proof.StockBswapDispatchWitness

#print axioms Backend.Stock.Proof.stock_source_opcode_inventory
#print axioms Backend.Stock.Proof.stock_neg_opcode_inventory
#print axioms Backend.Stock.Proof.stock_bswap_opcode_inventory
#print axioms Backend.Stock.Proof.stock_bitrev_opcode_inventory
#print axioms Backend.Stock.Proof.stock_selected_source_opcode
#print axioms Backend.Stock.Proof.stock_selected_source_opcode_ids
#print axioms Backend.Stock.Proof.stock_lower_source_record_opcode_ids
#print axioms Backend.Stock.Proof.stock_selected_neg_rule
#print axioms Backend.Stock.Proof.stock_selected_bswap_rule
#print axioms Backend.Stock.Proof.stock_selected_bitrev_rule
#print axioms Backend.Stock.Proof.stock_lower_neg_source_by_instruction
#print axioms Backend.Stock.Proof.stock_lower_bitrev_source_by_instruction
#print axioms Backend.Stock.Proof.stock_lower_bswap_source_by_instruction
#print axioms Backend.Stock.Proof.Neg.DispatchWitness.stock_lower_neg_dispatch_source_witness
#print axioms Backend.Stock.Proof.ScalarBit.BitrevDispatchWitness.stock_lower_bitrev_dispatch_source_witness
#print axioms Backend.Stock.Proof.ScalarBit.BswapDispatchWitness.stock_lower_bswap_dispatch_source_witness

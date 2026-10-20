import FV.Backend.Proof.StockArithmeticEntryWitness
import FV.Backend.Proof.StockEntryLoadsWitness
import FV.Backend.Proof.StockEntrySeedWitness

#print axioms Backend.Stock.Proof.entered_source_abi_row
#print axioms Backend.Stock.Proof.entered_source_row_value
#print axioms Backend.Stock.Proof.mapped_entry_dense_nodup
#print axioms Backend.Stock.Proof.mapped_entry_reg
#print axioms Backend.Stock.Proof.mapped_entry_code
#print axioms Backend.Stock.Proof.mapped_entry_prelude_preserves
#print axioms Backend.Stock.Proof.mapped_entry_prelude_fixed
#print axioms Backend.Stock.Proof.stock_lower_entry_assembly
#print axioms Backend.Stock.Proof.stock_lower_entry_prelude_refines
#print axioms Backend.Stock.Proof.stock_lower_entered_values_guarded
#print axioms Backend.Stock.Proof.ArithmeticBody.actual_arithmetic_return_refines_at
#print axioms Backend.Stock.Proof.ArithmeticBody.actual_arithmetic_entry_return_refines
#print axioms Backend.Stock.Proof.ArithmeticBody.actual_arithmetic_entry_return_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.EntryLoadsWitness.stack_whole_entry_prelude_witness -- witness: native_decide
#print axioms Backend.Stock.Proof.EntrySeedWitness.unused_whole_entry_prelude_witness -- witness: native_decide

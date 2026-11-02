import FV.Backend.Proof.StockPrologueClass
import FV.Backend.Proof.StockPrologueSelect
import FV.Backend.Proof.StockPrologueSource
import FV.Backend.Proof.StockPrologueInput
import FV.Backend.Proof.StockPrologueDomain
import FV.Backend.Proof.StockDiagnosticChecker
import FV.Backend.Proof.StockPrologueCodeCore
import FV.Backend.Proof.StockPrologueCode

#print axioms Clif.StockPrologueSource.source_entry
#print axioms Clif.StockPrologueSource.source_body
#print axioms Clif.StockPrologueSource.source_memory_roundtrip
#print axioms Clif.StockPrologueSource.complete_source_witness
#print axioms Backend.Stock.Prologue.systemV_i64_source
#print axioms Backend.Stock.Prologue.systemV_i64_source_witness
#print axioms Backend.Stock.Prologue.systemV_i64_context_scope
#print axioms Backend.Stock.Prologue.systemV_i64_lowering_domain
#print axioms Backend.Stock.DiagnosticChecker.lowerCheck_with_diagnostics
#print axioms Backend.Stock.Prologue.systemV_i64_code_and_success
#print axioms Backend.Stock.Prologue.lowerCheck_eraseDiagnostics
#print axioms Backend.Stock.Prologue.systemV_i64_checked_output
#print axioms Backend.Stock.Prologue.eligible_sound
#print axioms Backend.Stock.Prologue.source_eligible
#print axioms Backend.Stock.Prologue.eligible_checked_output
#print axioms Backend.Stock.Prologue.eligible_success_and_edges
#print axioms Backend.Stock.Production.outside_class
#print axioms Backend.Stock.Production.failed_attempt
#print axioms Backend.Stock.Production.eligible_output
#print axioms Backend.Stock.Production.eligible_checked_output
#print axioms Backend.Stock.Production.d0_outside_class
#print axioms Backend.Stock.Production.preserves_d0

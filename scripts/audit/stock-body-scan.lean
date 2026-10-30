import FV.Backend.Proof.StockLowerOutputs
import FV.Backend.Proof.StockRetProgress
import FV.Backend.Proof.StockScanProgress

#print axioms Isle.Interp.selectRule_restate_inv
#print axioms Backend.Stock.Proof.LowerProjection.scoped_of_calls
#print axioms Backend.Stock.Proof.Coverage.stock_covStmt_ok
#print axioms Backend.Stock.Proof.Coverage.lower_nop_opcode
#print axioms Backend.Stock.Proof.Coverage.stock_nomatch_of_argsFail
#print axioms Backend.Stock.Proof.Coverage.stock_stmt_int_out
#print axioms Backend.Stock.Proof.LowerProjection.retData_eq
#print axioms Backend.Stock.Proof.LowerProjection.stock_ret_backend
#print axioms Backend.Stock.Proof.LowerProjection.lower_ret_scope
#print axioms Backend.Stock.Proof.LowerProjection.ret_rules_scoped
#print axioms Backend.Stock.Proof.LowerProjection.stock_runTerm_ret_ok
#print axioms Backend.Stock.Proof.ScanProgress.buildCtx_quiet
#print axioms Backend.Stock.Proof.ScanProgress.scan_ok
#print axioms Backend.Stock.Proof.ScanProgress.bindResults_ok
#print axioms Backend.Stock.Proof.ScanProgress.emit_stmt_ok
#print axioms Backend.Stock.Proof.ScanProgress.emit_ret_ok
#print axioms Backend.Stock.Proof.ScanProgress.scanBlock_ok
#print axioms Backend.Stock.Proof.ScanProgress.lowerBlockCore_ret_ok
#print axioms Backend.Stock.Proof.ScanProgress.lowerBlockCore_ret_ok_witness -- witness: native_decide

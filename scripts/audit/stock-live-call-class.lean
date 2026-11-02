import FV.E2E.StockLiveCallWitness
import FV.E2E.StockLiveCallProvider
import FV.Backend.Lowering.StockLiveCallRoutes
import FV.E2E.StockLiveCallDomain
import FV.E2E.StockLiveCallNI
import FV.E2E.StockLiveCallFlags
import FV.E2E.StockLiveCallRun
import FV.E2E.StockLiveCallFixture
#print axioms Backend.Stock.Proof.LiveCallArithmetic.virtual_live
#print axioms Backend.Stock.Proof.LiveCallArithmetic.source_live
#print axioms Backend.Stock.Proof.LiveCallArithmetic.call_then_add
#print axioms Backend.Stock.Proof.LiveCallArithmetic.sum_holds
#print axioms Backend.Stock.Proof.LiveCallArithmetic.source_call_continues
#print axioms Backend.Stock.Proof.LiveCallArithmetic.continued_live
#print axioms Backend.Stock.Proof.LiveCallArithmetic.source_add_returns
#print axioms Backend.Stock.LiveCall.Layout.source_fields
#print axioms Backend.Stock.LiveCall.Layout.scan_fields
#print axioms Backend.Stock.LiveCall.check_sound
#print axioms Backend.Stock.LiveCall.callB_false
#print axioms Backend.Stock.LiveCall.prefixReads_of_append
#print axioms Backend.Stock.LiveCall.prelude_read_checks
#print axioms Backend.Stock.LiveCall.Layout.source_result
#print axioms Backend.Stock.LiveCall.Layout.return_function_for
#print axioms Backend.Stock.LiveCall.Layout.return_function
#print axioms Backend.Stock.LiveCall.source_call_notrap
#print axioms Backend.Stock.LiveCall.check_domain
#print axioms E2E.LiveCallFixture.actual_retained_and_saved -- witness: native_decide
#print axioms Backend.Stock.LiveCall.execute_tail
#print axioms Backend.Stock.LiveCall.Layout.ready
#print axioms Backend.Stock.LiveCall.Ready.sum_holds
#print axioms Backend.Stock.LiveCall.Ready.virtual_return
#print axioms Backend.Stock.LiveCall.Ready.execute
#print axioms Backend.Stock.LiveCall.Ready.execute_other
#print axioms Backend.Stock.LiveCall.checked_instruction
#print axioms Backend.Stock.LiveCall.noTls_of_codeCheck
#print axioms Backend.Stock.LiveCall.noTryCall_of_codeCheck
#print axioms E2E.backend_correct_world_niX_stock_live_call
#print axioms E2E.backend_correct_worldX_stock_live_call
#print axioms Backend.Stock.CheckedWith.lowerWithPrevious_retry
#print axioms Backend.Stock.CheckedWith.lowerWithPrevious_selects
#print axioms Backend.Stock.CheckedWith.candidate_stock
#print axioms Backend.Stock.CheckedWith.lowerWithPrevious_preserves
#print axioms Backend.Stock.CheckedWith.lowerWithPrevious_accepts
#print axioms Backend.Stock.LiveCall.lowerWithPrevious_retry
#print axioms Backend.Stock.LiveCall.lowerWithPrevious_selects
#print axioms Backend.Stock.LiveCall.candidate_stock
#print axioms Backend.Stock.LiveCall.lowerWithPrevious_preserves
#print axioms Backend.Stock.LiveCall.lowerWithPrevious_accepts
#print axioms Backend.Stock.LiveCall.lowerWithRoutes_default
#print axioms Backend.Stock.LiveCall.lowerWithRoutes_explicit
#print axioms Backend.Stock.LiveCall.candidate_domain
#print axioms Backend.Stock.LiveCall.lowerWithPrevious_origin
#print axioms E2E.LiveCallWitness.source_execution
#print axioms E2E.LiveCallWitness.complete_caller -- witness: native_decide
#print axioms E2E.LiveCallWitness.actual_provider -- witness: native_decide

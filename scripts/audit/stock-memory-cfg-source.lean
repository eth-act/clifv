import FV.E2E.StockMemoryPairedNopJump
import FV.Backend.Proof.StockMemoryRetainedReturnSpec
import FV.E2E.StockMemoryOmittedPairedScan
import FV.Backend.Proof.StockMemoryNopReturnBody
import FV.E2E.StockMemoryNopPairedBody
import FV.Backend.Proof.StockMemoryCfgReturnRefinesAt
import FV.Backend.Proof.StockMemoryCfgJumpDefined
import FV.Backend.Proof.StockMemoryCfgJumpReturnAt
import FV.Backend.Proof.StockMemoryNopBody
import FV.E2E.StockMemoryNopPairedPrelude
import FV.Backend.Proof.StockMemoryNopTrapBody
import FV.Backend.Proof.StockMemoryNopJumpSpec
import FV.Backend.Proof.StockMemoryCapturedFixture
import FV.E2E.StockMemoryPairedReturnEdge
import FV.E2E.StockMemoryPairedReturnEdgeBody
import FV.E2E.StockMemoryPairedJump
#print axioms Backend.Stock.Memory.stock_retained_load_return_spec
#print axioms Backend.Stock.Memory.RetainedLoadReturnSpec.nop_records
#print axioms E2E.StockMemory.stock_lower_omitted_paired_scan
#print axioms Backend.Stock.Memory.stock_nop_load_return_body
#print axioms E2E.StockMemory.stock_nop_load_return_paired_body
#print axioms Backend.Stock.Proof.OrdinaryBody.actual_ordinary_return_refines_at_block
#print axioms Backend.Stock.Proof.Inherited.local_jump_carry_returns_defined_of_body
#print axioms Backend.Stock.Proof.Control.jump_body_returns_at_of_body
#print axioms Backend.Stock.Memory.stock_nop_body
#print axioms E2E.StockMemory.stock_nop_paired_body
#print axioms Backend.Stock.Memory.stock_nop_body_with_traps
#print axioms Backend.Stock.Proof.Control.stock_lower_nop_jump_body_spec
#print axioms Backend.Stock.Memory.CapturedFixture.scope
#print axioms Backend.Stock.Memory.CapturedFixture.dominated
#print axioms Backend.Stock.Memory.CapturedFixture.lowered -- witness: native_decide
#print axioms Backend.Stock.Memory.CapturedFixture.entry_tag -- witness: native_decide
#print axioms Backend.Stock.Memory.CapturedFixture.nop_jump_witness -- witness: native_decide
#print axioms E2E.StockMemory.stock_lower_return_record_paired_runOkAt
#print axioms E2E.StockMemory.actual_ordinary_paired_return_refines_at_block
#print axioms E2E.StockMemory.paired_jump_body_returns_at_of_body

#print axioms E2E.StockMemory.stock_nop_paired_body_of_split
#print axioms E2E.StockMemory.paired_nop_jump_body_returns_at

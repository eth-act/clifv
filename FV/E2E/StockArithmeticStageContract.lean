import FV.Backend.Lowering.StockArithmetic
import FV.Backend.Regalloc
import FV.Backend.Asm
import FV.Backend.Encode

/-! Checked Stock artifact contract, independent of source-class correctness proofs. -/
namespace E2E
open Backend Backend.Proof.Driver
set_option autoImplicit false

/-- Both existing cleanup modes retain actual Stock provenance and the same
checked allocation/physical artifact contract. -/
structure CompiledStockArithmeticStage (f : Clif.Function) (cleanup : Bool) (k : Nat)
    (result : Stock.Result) (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  lower : Stock.lower f = .ok result
  prepare : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) = .ok vcp
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup result.code) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

end E2E

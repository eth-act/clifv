import FV.E2E.StockArithmeticStageContract

/-! The checked Stock artifact contract over any emitted code, without the provenance field. -/
namespace E2E
open Backend Backend.Proof.Driver
set_option autoImplicit false

/-- `CompiledStockArithmeticStage` for the emitted code `vc`. -/
structure CompiledStockCodeStage (cleanup : Bool) (k : Nat) (vc vcp : VCode) (rf : RFunc)
    (af : AFunc) (fa : FnAsm) (fb : FnBin) : Prop where
  prepare : Backend.prepare (Stock.Arithmetic.stage cleanup vc) = .ok vcp
  prepOk : prepCheck (Stock.Arithmetic.stage cleanup vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledStockArithmeticStage.code {f : Clif.Function} {cleanup : Bool} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (h : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    CompiledStockCodeStage cleanup k result.code vcp rf af fa fb :=
  ⟨h.prepare,h.prepOk,h.check,h.alloc,h.emit,h.layout⟩

end E2E

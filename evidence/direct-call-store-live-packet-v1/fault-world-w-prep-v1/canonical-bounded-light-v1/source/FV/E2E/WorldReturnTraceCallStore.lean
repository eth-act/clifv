import FV.E2E.WorldReturnTraceCore
import FV.E2E.StockCallStoreNIW

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The checked Stock call/store artifact keeps its complete ABI and paired field. -/
theorem worldReturnTraceProvider_callStore {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {result : Stock.Result} {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (checked : Stock.CallStore.check f result.code = true) {cleanup : Bool}
    (hc : CompiledStockArithmeticStage f cleanup k result vcp rf af fa fb) :
    WorldReturnTraceProvider p f result.code vcp rf af fa fb (ReturnABI f) where
  run := by
    intro X syms slotOff env K F c covered calls indirect symbols slot world args source
      entered related arguments explicit fuel
    exact backend_correct_world_niX_stock_call_store_returnW hsub checked hc
      covered calls indirect symbols slot entered related arguments fuel

end E2E

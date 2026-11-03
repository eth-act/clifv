import FV.E2E.StockAcquireActEntryKeep
import FV.E2E.StockArithmeticStageContract
import FV.Backend.Proof.StockAcquireTwoLoadCodeNoTls

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Both actual preparation modes derive the call/TLS facts needed to keep the original mapping's unwritable bytes.
No caller supplies a no-call or no-TLS certificate. -/
-- witness: native_decide
theorem two_load_actEntry_keep {k : Nat} {result : Stock.Result} {vc : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result vc rf af fa fb)
    {K : Nat} {F G S : BitVec 64 → Prop} {X : ExtSem} {H : ArmHooks}
    {base ra : BitVec 64} {initial world : Arm.ArmState}
    (entry : ActEntry vc rf af fa fb K F G X H base ra initial world)
    (stackAvoids : ∀ a,S a → ¬ StackBelow (frameDrop af+K) (spv initial) a) :
    ActEntry vc rf af fa fb K (fun a => F a ∨ S a) (fun a => G a ∨ S a) X H base ra initial world := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ := AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  exact actEntry_keep_of_no_calls_no_tls entry
    (AcquireTwoLoadPrefix.two_load_prepared_no_call_sites hc.lower scope dominated size events schedule hc.prepare)
    (AcquireTwoLoadPrefix.two_load_prepared_no_tls hc.lower scope dominated size events schedule hc.prepOk) stackAvoids

end E2E.StockAcquirePending

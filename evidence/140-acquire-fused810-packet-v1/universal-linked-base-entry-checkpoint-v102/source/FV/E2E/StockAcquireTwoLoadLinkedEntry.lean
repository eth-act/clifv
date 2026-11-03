import FV.E2E.StockAcquireLinkedBaseEntry
import FV.E2E.StockArithmeticStageContract
import FV.Backend.Proof.StockAcquireTwoLoadCodeNoTls

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Actual preparation discharges both site predicates from the fixed lowering.
The original base fields supply the unconditional activation fields. -/
-- witness: native_decide
theorem two_load_linked_actEntry (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {M k : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb)
    {F G : BitVec 64 → Prop} {ra : BitVec 64} {s world : Arm.ArmState}
    (basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (L.Hb.call d s) = Arm.r .PC s+4)
    (baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs,w') →
      Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program)
    (entry : L.MachEntry κ M AcquireTwoLoadPrefix.function F G ra s world) :
    ActEntry (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb (κ M AcquireTwoLoadPrefix.function)
      F G (L.X κ M AcquireTwoLoadPrefix.function F) (L.hooks M)
      (L.A AcquireTwoLoadPrefix.function).base ra s world ∧
    ArmStepX (L.X κ M AcquireTwoLoadPrefix.function F) (L.hooks M)
      (L.A AcquireTwoLoadPrefix.function).fa = L.mach M AcquireTwoLoadPrefix.function := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  exact ⟨linked_actEntry_of_machEntry_no_calls_no_tls L basePc baseExt entry
    (AcquireTwoLoadPrefix.two_load_prepared_no_call_sites hc.lower scope dominated size events schedule hc.prepare)
    (AcquireTwoLoadPrefix.two_load_prepared_no_tls hc.lower scope dominated size events schedule hc.prepOk),
    linked_ArmStepX_eq_mach L κ M AcquireTwoLoadPrefix.function F⟩

end E2E.StockAcquirePending

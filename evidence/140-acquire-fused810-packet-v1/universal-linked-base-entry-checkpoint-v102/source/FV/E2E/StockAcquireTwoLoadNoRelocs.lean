import FV.E2E.StockAcquirePhysicalNoRelocs
import FV.E2E.StockAcquireTwoLoadModelStepF

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Actual lowering, both preparation modes, allocation and emission derive no relocations.
The emitted-family proof excludes TLS tails without adding a caller TLS condition. -/
-- witness: native_decide
theorem two_load_compiled_no_relocations (L : LinkSys) {k : Nat} {result : Stock.Result} {cleanup : Bool}
    (hc : CompiledStockArithmeticStage AcquireTwoLoadPrefix.function cleanup k result
      (L.A AcquireTwoLoadPrefix.function).vcp (L.A AcquireTwoLoadPrefix.function).rf
      (L.A AcquireTwoLoadPrefix.function).af (L.A AcquireTwoLoadPrefix.function).fa
      (L.A AcquireTwoLoadPrefix.function).fb) :
    (L.A AcquireTwoLoadPrefix.function).fb.relocs = [] := by
  obtain ⟨actual,event,lowered,scope,dominated,abi,size,events,schedule⟩ :=
    AcquireTwoLoadPrefix.original_two_load_schedule
  have equal := Except.ok.inj (lowered.symm.trans hc.lower)
  subst actual
  have allocated := two_load_allocated_no_hooks hc.lower scope dominated size events schedule hc.prepare hc.alloc
  exact layout_no_relocations hc.layout (emitFunc_no_relocs hc.emit allocated)

end E2E.StockAcquirePending

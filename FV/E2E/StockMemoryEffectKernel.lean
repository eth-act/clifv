import FV.E2E.StockMemoryValue
import FV.Backend.Proof.StockMemorySingleFixture

namespace E2E.StockMemoryEffectKernel
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Memory.SingleFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The first original source input passes its executable classifier. -/
theorem source_checked : Memory.sourceOk function = true := by native_decide

/-- Actual whole Stock lowering emits only concrete/value-equivalent effects. -/
theorem actual_effects : (match Stock.lower function with
    | .ok result => Memory.effectsOnly result.code
    | .error _ => false) = true := by decide +kernel

end E2E.StockMemoryEffectKernel

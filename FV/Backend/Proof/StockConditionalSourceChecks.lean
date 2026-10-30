import FV.Backend.Lowering.StockConditionalCfg
import FV.Backend.Proof.StockConditionalEmptyFixture
import FV.Backend.Proof.StockConditionalEmptyTrapSource

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- The original executable input checks accept both complete compatible
sources. This checks source conditions only; emitted code is proved separately. -/
theorem conditional_source_checks_witness :
    Stock.ConditionalCfg.sourceOk EmptyFixture.function = true ∧
    Stock.ConditionalCfg.sourceOk EmptyTrapFixture.function = true := by
  -- witness: native_decide (fixed original executable source checks only; no emitted-code fact)
  constructor <;> native_decide

end Backend.Stock.Proof.ConditionalValues

import FV.E2E.ProductionPipelineWith
import FV.E2E.DeadCleanupLinkCheck

namespace E2E.LinkCheck
open Backend
set_option autoImplicit false

/-- Retain the same source, stage, indices, oracle and allocator fallback. -/
theorem LinkInput.production_legacy_binding (I : LinkInput) (cleanup : Bool) (fi : FnInput) :
    I.pipeProductionWith lowerFunction cleanup fi =
      I.pipeOfWithLowering lowerFunction (productionStage cleanup) fi := by
  have same : Stock.D0.defaultLower = lowerFunction :=
    funext Stock.D0.defaultLower_eq_legacy
  unfold LinkInput.pipeProductionWith
  rw [same]
  cases run : I.pipeOfWithLowering lowerFunction (productionStage cleanup) fi <;> rfl

theorem LinkInput.production_cleanup_binding (I : LinkInput) (fi : FnInput) :
    I.pipeProductionWith lowerFunction true fi = I.pipeCleanupOf fi := by
  rw [I.production_legacy_binding]
  unfold LinkInput.pipeOfWithLowering LinkInput.pipeCleanupOf
  have same : Stock.D0.defaultLower = lowerFunction :=
    funext Stock.D0.defaultLower_eq_legacy
  simp only [pipeCleanup,pipeCleanupT,same,productionStage,Stock.Arithmetic.stage]

theorem LinkInput.results_cleanup_binding (I : LinkInput) :
    I.resultsProductionWith lowerFunction true = I.resultsCleanup := by
  simp only [LinkInput.resultsProductionWith,LinkInput.resultsCleanup,I.production_cleanup_binding]

end E2E.LinkCheck

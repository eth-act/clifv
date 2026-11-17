import FV.E2E.ActualCompilerModes
import FV.E2E.ActualPipelineCheck
import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.DeadCleanupLinkCheckT
import FV.E2E.LinkCheck
import FV.E2E.LinkIdxT
import FV.E2E.ProductionPipeline
import FV.E2E.ProductionPipelineWith
import FV.E2E.SemanticPipelineCheckT
import FV.E2E.SemanticPipelineCheckWith
import FV.E2E.SrcScopeFast
import FV.Link.ConstPhiCompile
import FV.Link.ExeInput
import FV.Link.Image
import FV.Link.ProductionImage
import FV.Link.ProductionImageWith
import FV.Link.ReturnPinCompileDefs
import FV.Link.SemanticCompileDefs
import FV.Link.SemanticCompileT
import FV.Link.TypedCompileModes
import FV.Link.TypedStockShared

/-! #1062, #1071, #1076: `lean-link` and `link-check` at real-crate scale. Each `@[csimp]` lemma
states that the compiled replacement equals the original definition (the kernel and every theorem
see the original); the `…_of` lemmas state that the indexed checks equal the checks the
`@[csimp]` replacements of the program checks used before. -/

-- parallel tasks (`Task.spawn`/`Task.get` unfold to the sequential map)
#print axioms Link.parMap_eq
#print axioms E2E.LinkCheck.LinkInput.results_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsT_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsCleanup_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsCleanupT_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsWithLowering_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsTWithLowering_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsProduction_eq_par
#print axioms E2E.LinkCheck.LinkInput.resultsProductionWith_eq_par
#print axioms Link.LinkSpec.cp_eq_par
#print axioms Link.LinkSpec.cpChanged_eq_par
#print axioms Link.LinkSpec.cpFallbacks_eq_par
#print axioms Link.LinkSpec.withSizes_eq_par
#print axioms Link.LinkSpec.placedProduction_eq_par
#print axioms Link.LinkSpec.placedProductionWith_eq_par

-- the Stock route's pipeline run once per attempt
#print axioms Link.TypedCompilerWith.attempt_eq_fast
#print axioms Link.SemanticCompilerWith.attempt_eq_fast
#print axioms Link.SemanticCompilerWith.attemptT_eq_fast
#print axioms Link.ReturnPinCompilerWith.attempt_eq_fast

-- hash maps for the symbol table and the source scope
#print axioms Link.LinkSpec.input0_eq_fast
#print axioms E2E.LinkCheck.SrcScopeB_eq_fast

-- the program's scans per call site indexed (`LinkIdx`)
#print axioms E2E.LinkCheck.raCallIdxB_eq
#print axioms E2E.LinkCheck.linkChksWithI_of
#print axioms E2E.LinkCheck.linkChksWithTI_of
#print axioms E2E.LinkCheck.linkChksWithTSI_of
#print axioms E2E.LinkCheck.okRSemanticNI_eq_fast
#print axioms E2E.LinkCheck.okRSemanticFor_eq_fast
#print axioms E2E.LinkCheck.okRWithTS_eq_fast
#print axioms E2E.LinkCheck.okBCleanupTFast_eq

-- the typed Stock route with one cleanup pipeline and one Stock lowering per function (`lean-link`)
#print axioms Link.TypedStockShared.pipeTFrom_base
#print axioms Link.TypedStockShared.pipeProductionWith_eq
#print axioms Link.TypedStockShared.cleanupArts_placed
#print axioms Link.TypedStockShared.stockSteps_fst
#print axioms Link.TypedStockShared.stockSteps_placed
#print axioms Link.TypedStockShared.attemptTFrom_eq

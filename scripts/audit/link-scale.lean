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
import FV.E2E.StaticShare
import FV.E2E.SrcScopeFastT
import FV.Front.BundleFast

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
#print axioms E2E.LinkCheck.SrcScopeTB_eq_fast
#print axioms E2E.LinkCheck.SrcScopeTB_withDepth
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
#print axioms Link.TypedStockShared.stockRes_eq
#print axioms Link.TypedStockShared.attemptTFrom_eq

-- link-check: the integer and typed Stock per-function checks from one evaluation
#print axioms E2E.LinkCheck.semanticForOfNI_eq
#print axioms E2E.LinkCheck.withTSOfNI_eq

-- #1077: the bundle assembled with hash maps and in parallel (ruint, 232,604 functions)
#print axioms Front.eraseDupsH_eq
#print axioms Front.sortDedup_eq_F
#print axioms Front.localIds_eq_F
#print axioms Front.dataFnsOf_eq_F
#print axioms Front.PCgu.finTab_fin
#print axioms Front.finOfT_eq
#print axioms Front.scopingB_eq_F
#print axioms Front.mapM_eq_par
#print axioms Front.parseUnit_eq_F
#print axioms Front.assemble_eq_F
#print axioms Front.buildSpec_eq_F

-- #1108: distinct names with a hash set; the typed Stock route's checks evaluated once with
-- their failures
#print axioms E2E.LinkCheck.namesNodupB_eq
#print axioms E2E.LinkCheck.globalChksWith_eq_fast
#print axioms E2E.LinkCheck.progScopeWithB_eq_fast
#print axioms E2E.LinkCheck.progScopeInWithB_eq_fast
#print axioms Link.TypedStockShared.stockFails_isEmpty
#print axioms Link.TypedStockShared.attemptTFrom_stockFails
#print axioms E2E.LinkCheck.blrFastC_eq
#print axioms E2E.LinkCheck.indFastC_eq
#print axioms E2E.LinkCheck.linkChksWithTSX_of
#print axioms E2E.LinkCheck.allMay_eq
#print axioms E2E.LinkCheck.anyMay_eq
#print axioms E2E.LinkCheck.candFacts

-- #1108: the writer indexed (relocations, region bytes, data objects: the link map in hash maps,
-- each function's relocations by offset; the code map without comparing every pair), and the
-- program-level input conditions through the indirect-call index
#print axioms Link.RelocCtx.addrOf_of
#print axioms Link.RelocCtx.baseOf_of
#print axioms Link.RelocCtx.symAddr_of
#print axioms Link.relocIdx_getD
#print axioms Link.offsNodupB_eq
#print axioms Link.relocOkF_eq
#print axioms Link.relocsOkF_eq
#print axioms Link.relocsAllF_eq
#print axioms Link.resolveWordF_eq
#print axioms Link.artPush_toList
#print axioms Link.regionPush_toList
#print axioms Link.regionBA_eq
#print axioms Link.dataFastB_eq_fast
#print axioms Link.leanLink_eq_fast
#print axioms Link.DeadCleanup.leanLink_eq_fast
#print axioms Link.leanLinkWithResults_eq_fast
#print axioms E2E.LinkCheck.noBlrFastB_eq
#print axioms E2E.LinkCheck.rangesChainB_pairs
#print axioms E2E.LinkCheck.codeMapLinB_eq
#print axioms E2E.LinkCheck.codeMapB_eq_lin
#print axioms E2E.LinkCheck.indSiteFastB_eq
#print axioms E2E.LinkCheck.callScopeFastB_eq
#print axioms E2E.LinkCheck.indFastX_eq
#print axioms E2E.LinkCheck.progFnFastB_eq
#print axioms E2E.LinkCheck.progScopeFastB_eq_idx
#print axioms E2E.LinkCheck.progScopeInFastB_eq_idx

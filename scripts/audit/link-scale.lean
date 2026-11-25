import FV.E2E.ActualCompilerModes
import FV.E2E.PreparedReturnPinCalls
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
import FV.Link.ScopePlacement
import FV.Link.Ld.DataFast
import FV.E2E.BinCheckFast
import FV.E2E.GotTab
import FV.E2E.GotIdx
import FVTest.E2E.LinkProof

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
#print axioms E2E.LinkCheck.LinkInput.prog_eq_par
-- the input conditions do not read the placement (`lean-link` decides them once)
#print axioms E2E.LinkCheck.progScopeB_isSome
#print axioms E2E.LinkCheck.progScopeInB_isSome
#print axioms Link.inScopePar_withSizes
#print axioms Link.inScopeInPar_withSizes

-- #1108: the integer and return-pin routes' checks (the per-function checks in parallel, the
-- `blr`/indirect-call candidates by signature, the return-pin sites' entries by GOT name and
-- signature); `okRSemanticNI_eq_fast`, `okRSemanticFor_eq_fast` above, re-proved
#print axioms E2E.LinkCheck.blrFastI_eq
#print axioms E2E.LinkCheck.siteFastI_eq
#print axioms E2E.LinkCheck.linkChksWithIX_of
#print axioms E2E.LinkCheck.returnPinCands_of
#print axioms E2E.LinkCheck.returnPinSiteIdx_eq
#print axioms E2E.LinkCheck.returnPinsIdx_eq
#print axioms E2E.LinkCheck.okRReturnPinCalls_eq_fast
-- #1109: `lean-ld`'s plan checked against the data objects with the pieces indexed (the piece of
-- an address by binary search, each piece's relocation chain once, relocations from an offset)
#print axioms Link.Ld.itemsB_congr
#print axioms Link.Ld.objPlanWith_eq
#print axioms Link.Ld.relsFrom_drop
#print axioms Link.Ld.tailsArr_get
#print axioms Link.Ld.sfx_relsFrom
#print axioms Link.Ld.search_spec
#print axioms Link.Ld.find_spec
#print axioms Link.Ld.dataPlanF_eq
#print axioms Link.Ld.dataPlanB_eq_fast
#print axioms Link.Ld.Plan.specOkF_eq
#print axioms Link.Ld.specOkB_eq_fast
-- #1108: link-check's call graph (the stack bound) with each function's candidate edges indexed
-- by name and parameter types, one task per function
#print axioms E2E.StackBound.budCands_of
#print axioms E2E.StackBound.budSuccFast_eq_idx
-- #1145: link-check's GOT check with the relocated bytes in a hash set (one lookup per slot
-- byte instead of a scan of every relocation)
#print axioms E2E.GotTab.relocAtB_eq_contains
#print axioms E2E.GotTab.gotTabB_eq_fast
-- #1090: the GOT symbol of each `blr` site from a per-function index (one pass over the VCode)
-- instead of a scan of the whole VCode per site and per function the site may enter
#print axioms E2E.lookupMap_get
#print axioms E2E.GotIdx.syms_of
#print axioms E2E.gotB_flat
#print axioms E2E.GotIdx.ok_of
#print axioms E2E.GotIdx.got_of
#print axioms E2E.GotIdx.tab_get
#print axioms E2E.gotOf_eq_tab
#print axioms E2E.LinkCheck.all_filter_may
#print axioms E2E.LinkCheck.blrOk_may
#print axioms E2E.LinkCheck.blrOkC_may
#print axioms E2E.LinkCheck.siteWithOkG_may
#print axioms E2E.LinkCheck.siteWithOkCG_may
#print axioms E2E.LinkCheck.siteWithOkTCG_may
#print axioms E2E.LinkCheck.linkChksWithI_eq_got
#print axioms E2E.LinkCheck.linkChksWithTI_eq_got
#print axioms E2E.LinkCheck.linkChksWithTSI_eq_got
#print axioms E2E.LinkCheck.returnPinsIdx_eq_got
-- #1090: the lowering validators' context check with the function equality behind a call
-- (inlined ahead of the loops it made them super-linear: `check_sub` 154 s → 0.1 s)
#print axioms Backend.Proof.Driver.ctxOk_eq_fast
#print axioms Backend.Proof.Driver.ctxOkT_eq_fast

-- #1090: `inFix` without its blocks × values table (`fixSparse`: per block the sorted array of its
-- available values, passes until one changes nothing; the dense table's worklist removed 136.7M
-- of `check_sub`'s 167.6M pairs one by one): both compute the greatest solution of the constraints
#print axioms Backend.Proof.Driver.inFix_eq_sparse
#print axioms Backend.Proof.Driver.inFixSp?_eq
#print axioms Backend.Proof.Driver.Fix.fixSparse_eq
#print axioms Backend.Proof.Driver.Fix.fixSparse_spec
#print axioms Backend.Proof.Driver.Fix.dense_sol
#print axioms Backend.Proof.Driver.Fix.dense_great

-- #1090: link-check's FAIL details (`detail`) with the CLIF image's symbols in a hash map and the
-- failing function's facts computed once (per call site it tested every program function with a
-- list lookup among the symbols and a scan of the function's body: k256's projective test
-- executable, 19 functions, 972 s → 12.7 s)
#print axioms detail_eq_with
#print axioms detail_eq_fast

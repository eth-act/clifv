import FV.Link.LayoutProof
import FV.Link.DeadCleanupLayoutProof
import FV.Link.ActualImageProof
import FV.Link.ProductionImageProof
import FV.Link.ProductionImageWithProof
import FV.Link.ExeInputReach
import FV.Link.Correct
import FV.Link.DeadCleanupCorrect
import FVTest.Link.AlignedPoolT

-- #1061: the alignment-aware placement (`Link.offsA`) and the aligned region (`regionBytesA`)
#print axioms Link.alignW_dvd
#print axioms Link.offsA_ge
#print axioms Link.offsA_sep
#print axioms Link.offsA_end
#print axioms Link.offsA_mod4
#print axioms Link.offsA_aligned
#print axioms Link.offsA_nil
#print axioms Link.endA_nil
#print axioms Link.regionGo_getElem?
#print axioms Link.regionBytesA_length
#print axioms Link.regionBytesA_getElem?
#print axioms Link.region_wordsA
#print axioms Link.artOk_regionA
-- statements restated over the aligned placement (the compiler-side `progAddrs` changed)
#print axioms Link.LinkSpec.off_end
#print axioms Link.LinkSpec.off_sep
#print axioms Link.LinkSpec.addrs_name
#print axioms Link.LinkSpec.baseOf_name
#print axioms Link.LinkSpec.inputCleanup_baseOf_name
#print axioms Link.tab_placed
#print axioms Link.addr_inj
#print axioms Link.progAddrs_getElem
#print axioms Link.tab_home
#print axioms Link.DeadCleanup.tab_home
#print axioms Link.DeadCleanup.tab_placed
#print axioms Link.ActualImageProof.tab_placed
#print axioms Link.ProductionImageProof.tab_placed
#print axioms Link.ProductionImageWithProof.tab_placed
#print axioms Link.pc_of_placed
-- statements unchanged, proofs over the aligned region
#print axioms Link.leanLink_placed
#print axioms Link.binOk_leanLink
#print axioms Link.DeadCleanup.leanLink_placed
-- witnesses
#print axioms E2E.AlignedPoolTWitness.checks_true -- witness: native_decide
#print axioms E2E.AlignedPoolTWitness.lit_aligned -- witness: native_decide
#print axioms E2E.AlignedPoolTWitness.correct_spec -- witness: native_decide
#print axioms E2E.AlignedPoolTWitness.addrs_name_old_false -- witness: native_decide

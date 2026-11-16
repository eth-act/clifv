import FV.Backend.Proof.DriverCheckCF
import FV.Backend.Proof.LowerSimUCheckTC
import FV.Backend.CleanupStage
import FV.Backend.SkipDead
import FV.E2E.RegLevelUTry

/-! #1057: the validators in linear memory. Each `@[csimp]` lemma states that the compiled
replacement equals the original definition (the kernel and every theorem see the original). -/

#print axioms Backend.Proof.Driver.lowBlocksLite_eq
#print axioms Backend.Proof.Driver.inFix_eq_fast
#print axioms Backend.Proof.Driver.lowerCheck_eq_lite
#print axioms Backend.Proof.Driver.lowerCheckT_eq_lite
#print axioms Backend.Proof.Driver.lowerCheckTC_eq_lite
#print axioms Backend.Proof.Driver.lowerCheckTCF_eq_lite
#print axioms Backend.Proof.Driver.unwCheck_eq_lite
#print axioms Backend.Proof.Driver.unwCheckTC_eq_lite
#print axioms Backend.Proof.Driver.skipDead_eq_impl
#print axioms Backend.skipStage_eq_impl
#print axioms Backend.Proof.padsNonzeroB_eq_fast

import FV.Backend.Asm
import FV.Opt.Legal
import FV.Opt.LegalExn
import FV.Opt.OptimizeX
import FV.E2E.LinkScopeInputDefsTC
import FV.E2E.LinkScopeFast

/-! #1074: large functions in polynomial time. Each `@[csimp]` lemma states that the compiled
replacement equals the original definition (the kernel and every theorem see the original). -/

#print axioms Backend.repAt_eq_repChain
#print axioms Backend.repAt_eq_chain
#print axioms Backend.emitFunc_eq_fast
#print axioms Opt.Legal.termOk_eq_F
#print axioms Opt.Legal.codeOk_eq_F
#print axioms Opt.Legal.blockOk_eq_F
#print axioms Opt.Legal.checkW_eq_F
#print axioms Opt.Legal.termExnOk_eq_F
#print axioms Opt.Legal.exnOk_eq_F
#print axioms Opt.closedB_eq_fast
#print axioms Backend.Proof.Driver.ptrSet_contains
#print axioms Backend.Proof.Driver.stmtInB_eq_W
#print axioms Backend.Proof.Driver.driverInB_eq_F
#print axioms E2E.LinkCheck.stmtInTCB_eq_W
#print axioms E2E.LinkCheck.driverInTCB_eq_F
#print axioms E2E.LinkCheck.outScopeWithB_eq_fast

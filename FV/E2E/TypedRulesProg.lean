module

public import FV.E2E.FinalT
public import FV.Backend.Proof.IselCtlUnmatchTI
public import FV.Backend.Proof.IselCtlTermTI
public import FV.Backend.Proof.IselCtlBranchTI
public import FV.Backend.Proof.IselCtlTryTI

@[expose] public section

/-!
# The typed control families hold for the exported program (S11e5 Stage C, slice 5)

`TypedRules` (the ten typed control families the typed final theorems take, `E2E/FinalT.lean`)
for `Isle.Aarch64.program`: the pinned call families (`callRulesCorrectTP_program`,
`indRulesCorrectTP_program`, `tryRulesCorrectTP_program`, `tryIndRulesCorrectTP_program`), the
class-aware terminator rules (`lowerTermRulesCorrectT_program`), the branch rules
(`branchRulesCorrectT_program`) and the four unmatchability statements. Every `hT : TypedRules`
premise (`backend_correct_finalT`, `backend_correct_final_exT`, `backend_correct_final_ofT`, the
dead-cleanup, world and scope variants) is discharged by `typedRules_program`.
-/

namespace E2E

open Backend Backend.Proof

/-- **The typed control families hold for the exported program.** -/
theorem typedRules_program : TypedRules where
  calls := callRulesCorrectTP_program
  ind := indRulesCorrectTP_program
  term := lowerTermRulesCorrectT_program
  termUn := termUnmatchableT_program
  branch := branchRulesCorrectT_program
  branchEx := branchExcludedUnmatchableT_program
  try_ := tryRulesCorrectTP_program
  tryUn := tryUnmatchableT_program
  tryInd := tryIndRulesCorrectTP_program
  tryIndUn := tryIndUnmatchableT_program

end E2E

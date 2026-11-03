import FV.Backend.ABIReadCfg

/-! Regression witnesses for the ABI-read CFG boundary (#140): it admits the
bit-test branch, the island and the jump table on virtual integer registers,
and it keeps rejecting a bit-test branch on a physical register. -/
namespace E2E.ABIReadCfgTableWitness
open Backend
set_option autoImplicit false

theorem testBit_admitted :
    ABIReadCfg.additional (.testBitAndBranch .nz 1 2 (.vreg 3 .int) 5) = true := by decide

theorem island_admitted : ABIReadCfg.additional (.emitIsland 16) = true := by decide

theorem table_admitted :
    ABIReadCfg.additional (.jtSequence 1 [2,3] (.vreg 4 .int) (.vreg 5 .int) (.vreg 6 .int)) = true := by
  decide

theorem testBit_physical_rejected :
    ABIReadCfg.additional (.testBitAndBranch .z 1 2 (.x 0) 5) = false := by decide

end E2E.ABIReadCfgTableWitness

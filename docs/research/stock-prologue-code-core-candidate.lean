import Lean
import StockPrologueInputProbe
import FV.Backend.Lowering.StockD0

namespace Backend.Stock.PrologueProbe
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def eraseDiagnostics (vc : VCode) : VCode := {vc with name := "", rulesFired := #[]}

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock_stockPrologueCodeCoreProbe instDecidableEqVCode_stockPrologueCodeCoreProbe instDecidableEqExcept_stockPrologueCodeCoreProbe
attribute [local instance] instDecidableEqVBlock_stockPrologueCodeCoreProbe instDecidableEqVCode_stockPrologueCodeCoreProbe instDecidableEqExcept_stockPrologueCodeCoreProbe

macro "prologue_open_kernel_decide" : tactic => `(tactic|
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let proof ← Lean.Meta.mkDecideProof (← g.getType)
    g.assign proof)

/-- The first real Rust-prologue configuration: successful actual Stock output,
code agreement except diagnostics, and no omitted edge operands. Names and run
metadata are arbitrary; this is proof evidence, not a production selector. -/
theorem systemV_i64_code_and_success (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .systemVI64 runs)).isOk = true ∧
    (Stock.lower (source name .systemVI64 runs)).map
        (fun r => eraseDiagnostics (compact name r)) =
      (lowerFunction (source name .systemVI64 runs)).map eraseDiagnostics ∧
    ((Stock.lower (source name .systemVI64 runs)).toOption.map
      (fun r => r.edgeArgs.all (fun row => row.all (·.isEmpty)))).getD false = true := by
  prologue_open_kernel_decide


#print axioms systemV_i64_code_and_success
end Backend.Stock.PrologueProbe

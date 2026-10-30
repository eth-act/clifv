import Lean
import FV.Backend.Lowering.StockPrologue

namespace Backend.Stock.Prologue.AllConfigurations
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV
attribute [local instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV

def eraseDiagnostics (v : VCode) : VCode := {v with name := "",rulesFired := #[]}

macro "all_prologue_kernel_decide" : tactic => `(tactic|
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let proof ← Lean.Meta.mkDecideProof (← g.getType)
    g.assign proof)

theorem all_configurations_code_and_success (name : String) (runs : List Clif.RunCommand)
    (c : Configuration) :
    (Stock.lower (Prologue.source name c runs)).isOk = true ∧
    (Stock.lower (Prologue.source name c runs)).map
      (fun r => eraseDiagnostics (compact name r)) =
      (lowerFunction (Prologue.source name c runs)).map eraseDiagnostics ∧
    ((Stock.lower (Prologue.source name c runs)).toOption.map
      (fun r => r.edgeArgs.all (fun row => row.all (·.isEmpty)))).getD false = true := by
  cases c <;> all_prologue_kernel_decide


end Backend.Stock.Prologue.AllConfigurations

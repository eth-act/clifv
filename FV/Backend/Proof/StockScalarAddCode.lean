import Lean
import FV.Backend.Lowering.StockScalarAdd
import FV.Backend.Proof.StockPrologueCodeCore
set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV
attribute [local instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV

abbrev CodeFacts (name : String) (runs : List Clif.RunCommand) (c : Configuration) : Prop :=
    (Stock.lower (source name c runs)).isOk = true ∧
    (Stock.lower (source name c runs)).map
      (fun r => Prologue.eraseDiagnostics (compact name r)) =
      (lowerFunction (source name c runs)).map Prologue.eraseDiagnostics ∧
    ((Stock.lower (source name c runs)).toOption.map
      (fun r => r.edgeArgs.all (fun row => row.all (·.isEmpty)))).getD false = true

macro "scalar_add_kernel_decide" : tactic => `(tactic|
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let proof ← Lean.Meta.mkDecideProof (← goal.getType)
    goal.assign proof)

theorem code_defaultI32 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .defaultI32 := by
  unfold CodeFacts
  scalar_add_kernel_decide

theorem code_systemVI32 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .systemVI32 := by
  unfold CodeFacts
  scalar_add_kernel_decide

theorem code_fastI32 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .fastI32 := by
  unfold CodeFacts
  scalar_add_kernel_decide

theorem code_defaultI64 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .defaultI64 := by
  unfold CodeFacts
  scalar_add_kernel_decide

theorem code_systemVI64 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .systemVI64 := by
  unfold CodeFacts
  scalar_add_kernel_decide

theorem code_fastI64 (name : String) (runs : List Clif.RunCommand) :
    CodeFacts name runs .fastI64 := by
  unfold CodeFacts
  scalar_add_kernel_decide

/-- Actual complete-function Stock success, diagnostic-only code agreement and
empty edge operands for arbitrary names and metadata. Operands are unrestricted
runtime parameters; no legacy computation or comparison is used by selection. -/
theorem code_and_success (name : String) (runs : List Clif.RunCommand) (c : Configuration) :
    CodeFacts name runs c := by
  cases c with
  | defaultI32 => exact code_defaultI32 name runs
  | systemVI32 => exact code_systemVI32 name runs
  | fastI32 => exact code_fastI32 name runs
  | defaultI64 => exact code_defaultI64 name runs
  | systemVI64 => exact code_systemVI64 name runs
  | fastI64 => exact code_fastI64 name runs

end Backend.Stock.ScalarAdd

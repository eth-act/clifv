import Lean
import FV.Backend.Lowering.StockD0
import FV.Backend.Proof.DriverCheck

namespace Backend.Stock.PrologueProbe
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def source (name : String) (c : Configuration) (runs : List Clif.RunCommand) : Clif.Function :=
  { D0.source name c runs with blocks := [
      { id := 0, params := [(0, valueType c)], body := [{inst := .nop}],
        term := .jump {block := 1, args := []} },
      { id := 1, body := [{inst := .nop}], term := .ret [0] }] }

def eraseDiagnostics (vc : VCode) : VCode := {vc with name := "", rulesFired := #[]}

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV
attribute [local instance] instDecidableEqVBlock instDecidableEqVCode instDecidableEqExcept_fV

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

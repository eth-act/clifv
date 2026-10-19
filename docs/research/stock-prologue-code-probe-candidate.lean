import Lean
import StockPrologueInputProbe
import FV.Backend.Lowering.StockD0
import FV.Backend.Proof.DriverCheck
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.PrologueProbe
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

def eraseDiagnostics (vc : VCode) : VCode := {vc with name := "", rulesFired := #[]}

deriving instance DecidableEq for VBlock
deriving instance DecidableEq for VCode
deriving instance DecidableEq for Except
attribute [-instance] instDecidableEqVBlock_stockPrologueCodeProbe instDecidableEqVCode_stockPrologueCodeProbe instDecidableEqExcept_stockPrologueCodeProbe
attribute [local instance] instDecidableEqVBlock_stockPrologueCodeProbe instDecidableEqVCode_stockPrologueCodeProbe instDecidableEqExcept_stockPrologueCodeProbe

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

/-- The actual Stock output itself passes the existing source-shape and SSA
validator. Its diagnostic history is retained. This supplies a fixed class proof,
not a new caller premise or a runtime Stock/legacy output comparison. -/
theorem systemV_i64_checked_output (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .systemVI64 runs)).map
      (fun r => Backend.Proof.Driver.lowerCheck (source name .systemVI64 runs)
        (compact name r)) = .ok true := by
  let f := source name .systemVI64 runs
  have domain : Backend.Proof.Driver.dominatedB f = true ∧
      Backend.Proof.Driver.lowerScopeB f = true := by
    prologue_open_kernel_decide
  obtain ⟨success, code, edges⟩ := systemV_i64_code_and_success name runs
  change (Stock.lower f).map
    (fun r => Backend.Proof.Driver.lowerCheck f (compact name r)) = .ok true
  change (Stock.lower f).isOk = true at success
  change (Stock.lower f).map (fun r => eraseDiagnostics (compact name r)) =
    (lowerFunction f).map eraseDiagnostics at code
  cases run : Stock.lower f with
  | error e => simp only [run, Except.isOk, Bool.false_eq_true] at success
  | ok r =>
    cases legacy : lowerFunction f with
    | error e =>
      simp only [run, legacy, Except.map] at code
      cases code
    | ok vc =>
      simp only [run, legacy, Except.map] at code
      have same := congrArg (Backend.Proof.Driver.lowerCheck f) (Except.ok.inj code)
      change Backend.Proof.Driver.lowerCheck f (compact name r) =
        Backend.Proof.Driver.lowerCheck f vc at same
      have accepted := Backend.Proof.Driver.lowerCheck_complete
        (Backend.Proof.Driver.dominated_of domain.1)
        (Backend.Proof.Driver.lowerScope_of domain.2) legacy
      simp only [run, Except.map]
      rw [same, accepted]

#print axioms systemV_i64_checked_output

#print axioms systemV_i64_code_and_success
end Backend.Stock.PrologueProbe

import FV.Backend.Proof.StockScalarAddCode
import FV.Backend.Proof.StockPrologueCode
import FV.Backend.Proof.StockDiagnosticChecker
import FV.Backend.Proof.StockScalarAddDomain
import FV.Backend.Proof.LowerComplete

set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- The actual Stock output itself passes the existing source-shape and SSA
validator. Its diagnostic history is retained. This supplies a fixed class proof,
not a new caller premise or a runtime Stock/legacy output comparison. -/
theorem checked_output (name : String) (runs : List Clif.RunCommand) (c : Configuration) :
    (Stock.lower (source name c runs)).map
      (fun r => Backend.Proof.Driver.lowerCheck (source name c runs)
        (compact name r)) = .ok true := by
  let f := source name c runs
  have domain := lowering_domain name runs c
  obtain ⟨success, code, edges⟩ := code_and_success name runs c
  change (Stock.lower f).map
    (fun r => Backend.Proof.Driver.lowerCheck f (compact name r)) = .ok true
  change (Stock.lower f).isOk = true at success
  change (Stock.lower f).map (fun r => Prologue.eraseDiagnostics (compact name r)) =
    (lowerFunction f).map Prologue.eraseDiagnostics at code
  cases run : Stock.lower f with
  | error e =>
    rw [run] at success
    change false = true at success
    cases success
  | ok r =>
    cases legacy : lowerFunction f with
    | error e =>
      simp only [run, legacy, Except.map] at code
      cases code
    | ok vc =>
      simp only [run, legacy, Except.map] at code
      have same := congrArg (Backend.Proof.Driver.lowerCheck f) (Except.ok.inj code)
      rw [Prologue.lowerCheck_eraseDiagnostics, Prologue.lowerCheck_eraseDiagnostics] at same
      have accepted := Backend.Proof.Driver.lowerCheck_complete
        domain.1 domain.2 legacy
      simp only [run, Except.map]
      rw [same, accepted]


end Backend.Stock.ScalarAdd

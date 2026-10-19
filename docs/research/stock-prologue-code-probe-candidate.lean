import StockPrologueCodeCoreProbe
import StockDiagnosticCheckerProbe
import StockPrologueDomainProbe
import FV.Backend.Proof.LowerComplete

namespace Backend.Stock.PrologueProbe
open D0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- Diagnostic fields do not affect the checker; prove this before specializing
its source, so transport never evaluates the concrete CFG dataflow fixpoint. -/
theorem lowerCheck_eraseDiagnostics (f : Clif.Function) (vc : VCode) :
    Backend.Proof.Driver.lowerCheck f (eraseDiagnostics vc) =
      Backend.Proof.Driver.lowerCheck f vc := by
  exact DiagnosticCheckerProbe.lowerCheck_with_diagnostics f vc "" #[]

/-- The actual Stock output itself passes the existing source-shape and SSA
validator. Its diagnostic history is retained. This supplies a fixed class proof,
not a new caller premise or a runtime Stock/legacy output comparison. -/
theorem systemV_i64_checked_output (name : String) (runs : List Clif.RunCommand) :
    (Stock.lower (source name .systemVI64 runs)).map
      (fun r => Backend.Proof.Driver.lowerCheck (source name .systemVI64 runs)
        (compact name r)) = .ok true := by
  let f := source name .systemVI64 runs
  have domain := systemV_i64_lowering_domain name runs
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
      rw [lowerCheck_eraseDiagnostics, lowerCheck_eraseDiagnostics] at same
      have accepted := Backend.Proof.Driver.lowerCheck_complete
        domain.1 domain.2 legacy
      simp only [run, Except.map]
      rw [same, accepted]

#print axioms lowerCheck_eraseDiagnostics
#print axioms systemV_i64_checked_output

#print axioms systemV_i64_code_and_success
end Backend.Stock.PrologueProbe

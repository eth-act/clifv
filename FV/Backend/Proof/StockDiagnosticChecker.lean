import FV.Backend.Proof.DriverCheck
set_option autoImplicit false
namespace Backend.Stock.DiagnosticChecker
/-- Name and rule history are diagnostic; the actual checker and code are retained. -/
theorem lowerCheck_with_diagnostics (f : Clif.Function) (vc : VCode)
    (name : String) (rules : Array Isle.RuleId) :
    Proof.Driver.lowerCheck f {vc with name := name, rulesFired := rules} =
      Proof.Driver.lowerCheck f vc := by
  rfl
end Backend.Stock.DiagnosticChecker

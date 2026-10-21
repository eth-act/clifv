import FV.Backend.Proof.DriverCheck

/-! Candidate bridge for the next production class. Rule history is retained on
Stock output; changing diagnostic history does not change the M7 code check. This
is not an activation predicate or a replacement for actual source simulation. -/
namespace Backend.Stock.RuleHistoryBridge

open Backend.Proof.Driver

theorem lowerCheck_with_rules (f : Clif.Function) (vc : VCode)
    (rules : Array Isle.RuleId) :
    lowerCheck f {vc with rulesFired := rules} = lowerCheck f vc := by
  rfl

/-- This applies to actual output, retaining its own history. A future class
must prove the code relation internally; it must not demand it from callers. -/
theorem lowerCheck_of_same_code {f : Clif.Function} {stock legacy : VCode}
    (code : {stock with rulesFired := legacy.rulesFired} = legacy)
    (accepted : lowerCheck f legacy = true) : lowerCheck f stock = true := by
  have h := congrArg (lowerCheck f) code
  rw [lowerCheck_with_rules] at h
  exact h.trans accepted

#print axioms lowerCheck_with_rules
#print axioms lowerCheck_of_same_code
end Backend.Stock.RuleHistoryBridge

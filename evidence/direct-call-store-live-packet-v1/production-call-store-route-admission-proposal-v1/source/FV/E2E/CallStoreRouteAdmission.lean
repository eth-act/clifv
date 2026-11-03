import FV.Backend.SemanticABICheck

namespace Backend.SemanticABI
set_option autoImplicit false

/-- The additive checker retains every old call-check acceptance. -/
theorem retained_calls_callStores {f : Clif.Function} {vc : VCode}
    (accepted : checkCalls f vc = true) : checkCallStores f vc = true :=
  previous_check_call_stores (previous_check_live_calls (previous_check_result_calls accepted))

/-- The typed alternative remains available under the additive checker. -/
theorem retained_call_route_disjunction {f : Clif.Function} {vc : VCode} {typed : Bool}
    (accepted : (checkCalls f vc || typed) = true) :
    (checkCallStores f vc || typed) = true := by
  simp only [Bool.or_eq_true] at accepted ⊢
  exact accepted.elim (fun old => Or.inl (retained_calls_callStores old)) Or.inr

/-- Allocation, preparation, and actual object checks remain the same. -/
theorem retained_call_route_check {f : Clif.Function} {vc : VCode}
    {allocation prepared typed object : Bool}
    (accepted : allocation && prepared && (checkCalls f vc || typed) && object = true) :
    allocation && prepared && (checkCallStores f vc || typed) && object = true := by
  simp only [Bool.and_eq_true] at accepted ⊢
  rcases accepted with ⟨allocated,prepared,admitted,bytes⟩
  exact ⟨allocated,prepared,retained_call_route_disjunction admitted,bytes⟩

end Backend.SemanticABI
